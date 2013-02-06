//Copy from a packed array and retain packedness

var copyPacked = function(b) 
/*: [;L,Lb;] 
      (b: Ref(Lb)) / (Lb: {Arr(Int)|(packed v)} > lArrPro)  -> 
      Ref(L) / (L: { Arr(Int)| (packed v)} > lArrPro ) */ 
{
  var i = 0;
  var a  = /*: L {Arr(Int)|(packed v)} */ [];
  
  /*: (&i:i0:{Int|(>= v 0)}, L:{Arr(Int)|(and (packed v) (= (len v) i0))} > lArrPro)
      -> ( &i: sameType, L: {Arr(Int)|(packed v)} > lArrPro) */ 
  for ( ; i < b.length; i++) {
    a[i] = b[i];  
  }  
  return a;
};
