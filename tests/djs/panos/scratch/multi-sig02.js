/*: tyArr {Arr(Int)|(packed v)} > lArrPro */ "#define";
/*: tyObj { nodes: Arr(Int) }  > lObjPro */ "#define";
/*: (~lArr : tyArr) */ "#weak";
/*: (~lObj : tyObj) */ "#weak";

var foo = function(a)
/*: {(and
        (v:: (a: Ref(~lArr)) -> Top )
        (v:: (a: Ref(~lObj)) -> Top )
    )} */
{
  /*: a lA */ "#thaw";
  if (a) {
    if (isArray(a)) {
      //assert(/*: Ref(lA) */ (a));
      //var i /*: {Int|(>= v 0)} */ = 0;
      ///*: (&a: Ref(lA), lA: tyArr) -> sameExact */
      //for (i = 0; i < a.length; i += 1) {
      //  a[i];
      //}
      
      /*: a (~lArr, thwd lA) */ "#freeze";
    }
    else {
//      assert(/*: Ref(lO) */ (a));
      /*: a (~lObj, thwd lA) */ "#freeze";
    }
  }

};
