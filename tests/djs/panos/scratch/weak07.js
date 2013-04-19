var arrayMap = 
/*: [A,B; La, Lapro, Lr] (Ref(La), (A) -> B) 
      / (La: Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: Arr(B) > lArrPro) */ "#extern";

var f2 = function(name_) /*: (Str) -> Str */ {
  return "a";
};

/*: (~strArr: Arr(Str) > lArrPro) */ "#weak";

var isObject =  
/*: (value: Top) -> {Bool| (iff (= v true) (= (tag value) "object"))} */ "#extern";

var bar = function(value,tmp3)
/*: [;L,Lr] (value:Ref(L), tmp3: Ref(~strArr)) / (L: Arr(Int) > lArrPro) -> Top / () */ 
/* [;L] (value:Ref(L), tmp3: Ref(~strArr)) / (L: {}  > lObjPro) -> Top / () */ 
{

  //XXX: a needs to to be defined before the thawing... 
  var vv;
  var a;

  if (!isArray(value)) {

    /*: tmp3 ltmp3 */ "#thaw";
    assume(tmp3 != null);
    a = /*: [Str,Str; ltmp3,lArrPro, Lr] */ arrayMap(tmp3,f2);
    /*: tmp3 (~strArr, thwd ltmp3) */ "#freeze";    

  }
};

