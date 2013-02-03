var foo = function(a)
/*: { (and 
  (v :: (a: Ref(lArr)) / (lArr: { Arr(Int) | (packed v)} > lArrPro) -> Top / sameType)
  (v :: (a: Ref(lObj)) / (lObj: { bb: Str} > lObjPro ) -> Top / sameType)
  )} */
{

  if(isArray(a)) {
    var i /*: {Int | (>= v 0)} */ = 0;
    for (i = 0; i < a.length; i += 1) {
      a[i];
    }
  }
  else {
    assert(/*: Str */ (a.bb));
  }

};
