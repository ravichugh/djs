
var arraySlice =
  /*: [A;La,Lapro,Lr] (Ref(La), Int, Int) / (La: Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: Arr(A) > lArrPro) */ "#extern";


var foo = function(a) 
/*: (a:Ref) / (a: Top > a.pro) -> Top / sameExact */
{ };

/*: (~arr: Arr(Int) > lArrPro) */ "#weak";

var baz = function() /*: () -> Top  */ { };


//If you freeze, then the original location is lost so we have to remove it from
//the output heap!-------------------------------------------|
//                                                           v
var bar = function(a,b)
/*: [;L] (a:Ref(L), Bool) / (L: Arr(Int) > lArrPro) -> Top / () */ 
{
  
  /*: a (~arr, frzn) */ "#freeze";    

  assume(a != null);


};

