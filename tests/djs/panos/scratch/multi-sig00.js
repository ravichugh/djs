/*: tyArr {Arr(Int)|(packed v)} > lArrPro */ "#define";

var foo = function(a)
/*: {(and
        (v:: (a: Ref(lA)) / (lA: tyArr)-> Top / sameExact )
        (v:: (a: Int) -> Top )
    )} */
{
  
  if (isArray(a)) {
    assert(/*: Ref(lA) */ (a));
  }
  else {
    assert(/*: Int */ (a));
  }

};
