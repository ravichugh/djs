
var arraySlice =
  /*: [A;La,Lapro,Lr] (Ref(La), Int, Int) / (La: Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: Arr(A) > Lapro) */ "#extern";


var foo = function(a) 
/*: (a:Ref) / (a: Top > a.pro) -> Top / sameExact */
{ };


var baz = function() /*: () -> Top  */ { };

var bar = function(a,b)
/*: [;L,L1] (a:Ref(L), Bool) / (L: Arr(Int) > L1) -> Top / sameType */ 
{
  var vv;

  /*: (~arr: Arr(Int) > L1) */ "#weak";
  if(b) {
    vv = /*: [Int; L,L1,lsl2] */ arraySlice(a, 0, 0);
    /*: vv (~arr, frzn) */ "#freeze"; 
    /*: a (~arr, frzn) */ "#freeze";    
  }
  else {
    /*: a (~arr, frzn) */ "#freeze";    
    vv = a;
  }      
  
  /*: a L */ "#thaw";

};

