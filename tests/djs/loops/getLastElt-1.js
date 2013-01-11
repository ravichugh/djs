/*: goalType {(if (= (len arr) 0)
               then (Undef v)
               else (NotUndef v))} */ "#define";

var getLastElt = function(a)
    /*: (a:Ref) / (a: arr:{Arr(NotUndef)|(packed v)} > lArrPro)
     -> goalType / sameExact */ {
  var ret;
  var n = a.length;
  /*: (&i: i0:{Int|(>= v 0)},
       &ret: {(if (or (= i0 0) (= (len arr) 0))
               then (Undef v)
               else (NotUndef v))})
   -> (&i: Int, &ret: goalType) */
  for (var i = 0; i < n; i++) {
    ret = a[i];
  }
  return ret;
};

assert (getLastElt([   ]) === undefined);
assert (getLastElt([0  ]) !== undefined);
assert (getLastElt([0,1]) !== undefined);
