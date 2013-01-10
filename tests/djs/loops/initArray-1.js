/*: goalType {Arr(NotUndef)| (and (packed v) (= (len v) n))} */ "#define";
/*: goalTypeI {Arr(NotUndef)|(and (packed v) (= (len v) i0))} */ "#define";

var init = function(n)
    /*: [;L] (n:{Int|(>= v 0)}) / ()
     -> Ref(L) / (L: goalType > lArrPro) */ {

  var a = /*: L */ [];

  /*: (&i: i0:{Int|(and (>= v 0) (<= v n))}, L: goalTypeI > lArrPro)
   -> (&i: sameType, L: goalType > lArrPro) */
  for (var i = 0; i < n; i++) {
    a[i] = i;
  }
  return a;
};
