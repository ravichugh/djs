var makeCumulative = function(table) /*: [;L1,L2]
   [[table:Ref(L1)]] / [L1 |-> (_:Dict, L2)] -> Top / [L1 |-> (_:Dict, L2)] */ {
  var last = null;
  var c;
  /*: [Heap] [Heap ++
        &last |-> _:{(implies (not (= v null))
                              (and (v : Str)
                                   (objhas d v Heap L2)
                                  ((objsel d v Heap L2) : Num)))},
        &c |-> _:Str, &table |-> _:Ref(L1), L1 |-> (d:Dict, L2)]
     -> Top / sameType */
  for (c in table) {
    if (last) {
      if ((typeof table[c]) == "number") {
        table[c] = table[c] + table[last];
        last = c;
      }
    }
  }
};
