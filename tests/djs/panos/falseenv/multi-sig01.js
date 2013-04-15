/*: tyArr {Arr(Int)|(packed v)} > lArrPro */ "#define";
/*: tyObj { nodes: Arr(Int) }  > lObjPro */ "#define";

var foo = function(a)
/*: {(and
        (v:: (a: Ref(lA)) / (lA: tyArr)-> Top / sameExact )
        (v:: (a: Ref(lO)) / (lO: tyObj)-> Top / sameExact )
    )} */
{
  
  if (a) {
    if (isArray(a)) {
      assert(/*: Ref(lA) */ (a));
    }
    else {
      assert(/*: Ref(lO) */ (a));
    }
  }

};


