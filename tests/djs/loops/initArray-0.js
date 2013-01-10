/*: goalType {Arr(NotUndef)|
               (and (packed v)
                    (ite (< n 0) (= (len v) 0) (= (len v) n)))} */ "#define";

var init = function(n)
    /*: [;L] (n:Int) / ()
     -> Ref(L) / (L: goalType > lArrPro) */ {

  var a = /*: L */ [];

  /*: (&i: i0:{Int|(and (>= v 0) (ite (< n 0) TRU (<= v n))
                        (if (< n 0)
                         then (= (len l0) 0)
                         else (ite (< i0 n) (= (len l0) v) (= (len l0) n))))},
       L:  l0:{Arr(NotUndef)|(packed v)} > lArrPro) 
   -> (&i: {Int|(ite (< n 0) TRU (= v n))},
       L:  goalType > lArrPro) */
  for (var i = 0; i < n; i++) {
    a[i] = i;
  }
  return a;
};
