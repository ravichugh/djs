var getLastElt = function(a)
    /*: (a:Ref) / (a: {Arr(NotUndef)|(and (packed v) (> (len v) 0))} > lArrPro)
     -> NotUndef / sameExact */ {
  var ret;
  var n = a.length;
  /*: (&i: i0:{Int|(>= v 0)}, &ret: {(or (= i0 0) (NotUndef v))})
   -> (&i: Int, &ret: NotUndef) */
  for (var i = 0; i < a.length; i++) {
    ret = a[i];
  }
  return ret;
};

assert (getLastElt([0  ]) !== undefined);
assert (getLastElt([0,1]) !== undefined);
