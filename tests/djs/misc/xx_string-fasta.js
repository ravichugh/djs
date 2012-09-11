/*: makeCumulative :: [;L1,L2]
    (table:Ref(L1)) / (L1 |-> Dict > L2) -> Int / sameType */ "#type";

var makeCumulative = function(table) {
  var last = null;
  var c;
  /*: [Heap] Heap +
        (&last |-> {(implies (not (= v null))
                             (and (Str v) (Num (objsel [d] v Heap L2))))},
         &c |-> Str, &table |-> Ref(L1), L1 |-> d:Dict > L2)
   -> sameType */
  for (c in table) {
    if (last) {
      if ((typeof table[c]) == "number") {
        table[c] = table[c] + table[last];
        last = c;
      }
    }
  }
};
