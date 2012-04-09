/*: #define tyPassenger
    {Dict|(implies (has v "weight") ((sel v "weight") : Num))} */ "#define";

/*: [~lPass |-> (tyPassenger, lObjectProto)] */ "#weak";

var sumWeight = function(passengers, max_weight)
/*: [;L] [[passengers:Ref(L), max_weight:Num]]
       / [L |-> (a:{Arr(Ref(~lPass))|(packed v)}, lArrayProto), ~lPass |-> frzn,
          lObjectProto |-> (objpro:{Dict|(not (has v "weight"))}, lROOT)]
      -> Num / same */ {
  var i = 0, sum = 0, n = passengers.length;
  /*: [&i |-> _:{Int|(>= v 0)}, &sum |-> _:Num, &passengers |-> _:Ref(L),
       &max_weight |-> _:Num, &n |-> _:{(= v (len a))},
       L |-> (_:{(= v a)}, lArrayProto), ~lPass |-> frzn,
       lObjectProto |-> (_:{(= v objpro)}, lROOT)] -> sameType */
  for (; i < n; i++) {
    var p = passengers[i];
    /*: p lThaw1 */ "#thaw";
    if (p.weight) { sum += p.weight;   }
    else          { sum += max_weight; }
    /*: p (~lPass, thwd lThaw1) */ "#freeze";
  }
  return sum;
};
