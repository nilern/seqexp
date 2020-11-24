(ns net.cgrand.perfexp
  (:refer-clojure :exclude [+ * repeat +' *' cat compile])
  (:require [clojure.walk :as walk])
  (:import [java.util Arrays]))

;;;; # Compiler

(def ^:private label-ops
  #{:label :jump :fork> :fork<})

(def ^:private op->opcode
  (zipmap (conj label-ops :pred :save0 :save1) (range)))

(def ^:private opcode->op
  (zipmap (vals op->opcode) (keys op->opcode)))

(defmacro ^:private asm [& exprs]
  (let [gen (gensym 'gen)
        exprs (partition 2 exprs)]
    `(let [~gen (memoize gensym)]
       (concat
         ~@(map
             (fn [[op arg]]
               (let [op (keyword op)]
                 (if (contains? op->opcode op)
                   [op (if (contains? label-ops op)
                         `(~gen ~(keyword arg))
                         arg)]
                   (do
                     (assert (= op :include))
                     `(instructions ~arg)))))
             exprs)))))

(defn- patch
  "Resolve labels to offsets.
  (idempotent)"
  [instructions]
  (let [[insts labels] (reduce (fn [[insts labels] [op arg]]
                                 (if (= :label op)
                                   [insts (assoc labels arg (quot (count insts) 2))]
                                   [(conj insts op arg) labels]))
                               [[] {}] (partition 2 instructions))
        code-length (quot (count insts) 2)]
    (loop [pc 0, [op arg & rinsts] insts, insts []]
      (if (< pc code-length)
        (let [arg (if (contains? label-ops op)
                    (if-some [dest (get labels arg)]
                      (- dest pc)
                      arg)
                    arg)]
          (recur (inc pc) rinsts (conj insts op arg)))
        insts))))

(deftype ^:private CompiledPattern [opcodes args])

(defn- codegen [instructions]
  (let [inst-count (quot (count instructions) 2)
        bytecodes (byte-array inst-count)
        args (object-array inst-count)]
    (loop [pc 0, [op arg & rinsts] instructions]
      (if (< pc inst-count)
        (do
          (aset bytecodes pc (byte (doto (get op->opcode op) assert)))
          (aset args pc arg)
          (recur (inc pc) rinsts))
        (CompiledPattern. bytecodes args)))))

(defprotocol ^:private Regex
  (instructions [re]))

(extend-protocol Regex
  Object
  (instructions [x] (instructions #(= x %)))

  clojure.lang.Symbol
  (instructions [x] (instructions #(= x %)))

  clojure.lang.AFn
  (instructions [f] (asm pred f)))

(defrecord ^:private Pattern [ops]
  Regex
  (instructions [_] ops))

(defmacro ^:private asmpat [& exprs]
  `(->Pattern (asm ~@exprs)))

(declare as)

(defn compile [pat] (-> (as :match pat) instructions patch codegen))

;;;; # Seqexp Combinators

(defn cat
  "Concatenates several seqexps into one."
  [e & es]
  (->Pattern (to-array (mapcat instructions (cons e es)))))

(defmacro ^:private decline [decls & forms]
  `(do
     ~@forms
     ~@(walk/postwalk #(decls % %) forms)))

(decline {* *? + +? ? ?? repeat repeat?
          *' *'? +' +'? repeat' repeat'?
          fork> fork< fork< fork> :fork> :fork< :fork< :fork>}
         (defn *
           "Matches its body zero or more times.
            Exists in greedy (*) and reluctant (*?) variants."
           [e & es]
           (asmpat
             label start
             fork> end
             include (apply cat e es)
             jump start
             label end))

         (defn +
           "Matches its body one or more times.
            Exists in greedy (+) and reluctant (+?) variants."
           [e & es]
           (asmpat
             label start
             include (apply cat e es)
             fork< start))

         (defn ?
           "Matches its body zero or once.
            Exists in greedy (?) and reluctant (??) variants."
           [e & es]
           (asmpat
             fork> end
             include (apply cat e es)
             label end))

         (defn repeat
           "Matches its body min to max times (inclusive).
            Exists in greedy (repeat) and reluctant (repeat?) variants."
           ([n e]
            (repeat n n e))
           ([min max e]
            (cond
              (pos? min) (cat (apply cat (clojure.core/repeat min e)) (repeat 0 (- max min) e))
              (pos? max) (? e (repeat 0 (dec max) e))
              :else (asmpat))))

         (defn +'
           "Matches its body one or more times separated by sep.
            Exists in greedy (+') and reluctant (+'?) variants."
           [sep e & es]
           (asmpat
             jump start
             label loop
             include sep
             label start
             include (apply cat e es)
             fork< loop))

         (defn *'
           "Matches its body zero or more times, separated by sep.
            Exists in greedy (*') and reluctant (*'?) variants."
           [sep e & es]
           (? (apply +' sep e es)))

         (defn repeat'
           "Matches its body min to max times (inclusive) separated by sep.
            Exists in greedy (repeat') and reluctant (repeat'?) variants."
           ([n sep e]
            (repeat' n n sep e))
           ([min max sep e]
            (cond
              (pos? min) (cat e (repeat (dec min) (dec max) (cat sep e)))
              (pos? max) (? (repeat' 1 max sep e))
              :else (asmpat)))))

(defn |
  "Matches either of its arguments."
  ([e] e)
  ([e & es]
   (asmpat
     fork> l1
     include e
     jump l2
     label l1
     include (apply | es)
     label l2)))

(defn as
  "Like cat but saves the match as a group under the specified name.
   (:match and :rest are reserved names)."
  [name e & es]
  (asmpat
    save0 name
    include (apply cat e es)
    save1 name))

(def _ "Matches anything" (constantly true))

;;;; Pike VM

(defmacro ^:private opcode-case [op & body]
  (letfn [(convert-pat [pat]
            (if (symbol? pat)
              (doto (get op->opcode (keyword pat)) assert)
              (map convert-pat pat)))]
    `(case ~op
       ~@(->> body
              (partition 2)
              (mapcat (fn [[pat expr]] [(convert-pat pat) expr]))))))

(defn- make-bitset ^bytes [max-val]
  (byte-array (quot (dec (clojure.core/+ max-val 8)) 8)))

(defn- clear-bitset! [^bytes set] (Arrays/fill set (byte 0)))

(defn- bitset-set! [^bytes set, ^long v]
  (let [byte-index (quot v 8)
        bit-index (rem v 8)]
    (aset set byte-index (unchecked-byte (bit-or (aget set byte-index)
                                                 (bit-shift-left 1 bit-index))))
    nil))

(defn- bitset-contains? [^bytes set, ^long v]
  (let [byte-index (quot v 8)
        bit-index (rem v 8)]
    (= (bit-and (bit-shift-right (aget set byte-index) bit-index)
                1)
       1)))

(defprotocol RegisterBank
  (save0 [bank id v])
  (save1 [bank id v])
  (fetch [bank coll0 coll]))

(defprotocol ^:private IMatch
  (decode-match [self coll]))

(deftype ^:private Match [^long start, ^long end]
  Object
  (toString [_] (prn-str [start end]))

  IMatch
  (decode-match [_ coll] (take (- end start) (drop start coll))))

(extend-protocol RegisterBank
  clojure.lang.APersistentMap
  (save0 [m id start] (assoc m id (Match. start start)))
  (save1 [m id end] (update m id (fn [^Match match] (Match. (.-start match) end))))
  (fetch [m coll0 coll]
    (-> (reduce-kv (fn [acc k match] (assoc! acc k (decode-match match coll0)))
                   (transient {:rest coll})
                   m)
        persistent!)))

(defrecord ^:private TreeStackFrame [children, ^long start])

(defrecord ^:private MatchNode [children, ^long start, ^long end]
  IMatch
  (decode-match [_ coll] (take (- end start) (drop start coll))))

(extend-protocol RegisterBank
  clojure.lang.APersistentVector
  (save0 [stack _ start] (conj stack (TreeStackFrame. {} start)))
  (save1 [stack id end]
    ;; 'return' `node`:
    (let [^TreeStackFrame callee-frame (peek stack)
          node (MatchNode. (.-children callee-frame) (.-start callee-frame) end)
          stack (pop stack)]
      ;; Update 'caller' state:
      (update stack (dec (count stack))
              (fn [^TreeStackFrame caller-frame]
                (TreeStackFrame. (update (.-children caller-frame) id (fnil conj []) node)
                                 (.-start caller-frame))))))
  (fetch [stack coll0 coll]
    (letfn [(fetch-node [^MatchNode node]
              (fetch-children {:match (decode-match node coll0)}
                              (.-children node)))
            (fetch-children [acc children]
              (-> (reduce-kv (fn [m id children]
                               (assoc! m (if (vector? id) (peek id) id) (mapv fetch-node children)))
                             (transient acc)
                             children)
                  persistent!))]
      (fetch-children {:rest coll}
                      (.-children ^TreeStackFrame (peek stack))))))

(defprotocol ^:private IVMState
  (thread-count [state])
  (fork! [state pc matches])
  (truncate! [state]))

(deftype ^:private VMState [^:unsynchronized-mutable ^long nthreads pcs matchess]
  IVMState
  (thread-count [_] nthreads)

  (fork! [_ pc matches]
    (let [i nthreads]
      (set! nthreads (inc i))
      (aset ^longs pcs i ^long pc)
      (aset ^"[Ljava.lang.Object;" matchess i matches)))

  (truncate! [_] (set! nthreads 0)))

(defn- exec-automaton* [^CompiledPattern automaton coll0 registers]
  (let [^bytes opcodes (.-opcodes automaton)
        ^"[Ljava.lang.Object;" args (.-args automaton)
        inst-count (alength opcodes)
        visited (make-bitset inst-count)
        state (VMState. 0 (long-array inst-count) (object-array inst-count))
        state* (VMState. 0 (long-array inst-count) (object-array inst-count))

        add-thread! (fn [^long pos, ^VMState state, ^long pc, matches]
                      (clear-bitset! visited)
                      ;; Micro-optimization: lambda-lift `add!` by hand:
                      (letfn [(add! [^long pos, ^VMState state, ^long pc, matches]
                                (cond
                                  (< pc (alength opcodes))
                                  (when-not (bitset-contains? visited pc)
                                    (bitset-set! visited pc)
                                    (opcode-case (aget opcodes pc)
                                      jump (recur pos state (clojure.core/+ pc (long (aget args pc))) matches)
                                      fork> (do
                                              (add! pos state (inc pc) matches)
                                              (recur pos state (clojure.core/+ pc (long (aget args pc))) matches))
                                      fork< (do
                                              (add! pos state (clojure.core/+ pc (long (aget args pc))) matches)
                                              (recur pos state (inc pc) matches))

                                      save0 (recur pos state (inc pc) (save0 matches (aget args pc) pos))
                                      save1 (recur pos state (inc pc) (save1 matches (aget args pc) pos))

                                      pred (fork! state pc matches)))

                                  (= pc (alength opcodes)) (fork! state pc matches)

                                  :else nil))]
                        (add! pos state pc matches)))

        match-item (fn [^long pos, coll, ^VMState state, ^VMState state*]
                     (loop [i 0]
                       (when (< i (thread-count state))
                         (let [pc (aget ^longs (.-pcs state) i)
                               matches (aget ^"[Ljava.lang.Object;" (.-matchess state) i)]
                           (if (< pc inst-count)
                             (let [opcode (aget opcodes pc)
                                   arg (aget args pc)]
                               (opcode-case opcode
                                 pred (when (and coll (arg (first coll)))
                                        (add-thread! (inc pos) state* (inc pc) matches))
                                 #_"add-thread! makes other opcodes impossible at this point")
                               (recur (inc i)))
                             matches)))))]

    (add-thread! 0 state 0 registers)
    (loop [pos 0, coll (seq coll0), state state, state* state*, longest nil]
      (let [longest (or (match-item pos coll state state*) longest)]
        (if (and (> (thread-count state*) 0) coll)
          (do
            (truncate! state)
            (recur (inc pos) (next coll) state* state longest))
          (when longest
            (fetch longest coll0 (or coll ()))))))))

(defn exec-automaton [automaton coll] (exec-automaton* automaton coll {}))

(defn exec [re coll] (exec-automaton (compile re) coll))

(defn exec-tree-automaton [automaton coll]
  (exec-automaton* automaton coll [(TreeStackFrame. {} 0)]))

(defn exec-tree [re coll] (exec-tree-automaton (compile re) coll))
