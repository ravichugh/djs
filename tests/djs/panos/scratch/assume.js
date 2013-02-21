

var bar = function(a) /*: (a:Ref) / (a: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType */ {
  if (a[1]) {
    assert(/*: Str */ (a[1]));
    assert(/*: Int */ (a[1].length));  
  }
};

var foo = function(a) 
/*: (a:Ref) / (a: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType */
{  
  assume(typeof a[1] == "string");
  assert(/*: Str */ (a[1]));
  assert(/*: Int */ (a[1].length));   //FAILS
};

