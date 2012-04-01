// adapted from SunSpider string-fasta.js. added explicit tag-tests.

var makeCumulative = function(table)
/*: [;L1,L2] [[table:Ref(L1)]] / [L1 |-> (_:Dict, L2)]
          -> Top / [L1 |-> (_:Dict, L2)] */
{
  var last = null;
  var c;
  /*: [&c |-> _:Str,
       &last |-> _:{(implies (not (= v null)) (v : Str))},
       &table |-> _:Ref(L1),
       L1 |-> (_:Dict, L2)] -> sameType */
  for (c in table) {
    if (last) {
      if (typeof table[c] == "number" && typeof table[last] == "number") {
        table[c] = table[c] + table[last];
      }
    }
    last = c;
  }
};
