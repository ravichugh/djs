
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document /*: Ref(~lDocument) */ = null;

var quest = function(query, selector) 
/*: [; L;] (Ref(L), Ref(~lSelector)) / (L: { Arr(Ref(~lSelector)) | (packed v) } > lArrPro) -> Int / sameType */ 
{
  var i /*: Int */  = 0;

  switch (selector.op) {
    case "one":
           i = 1;
           break;
    case "two":
           i = 2;
           break;
    default:
           i = 3;
           break;
  };

//  //PV: The following works
//  if (selector.op == "one") {
//    i = 1;
//  }
//  else if (selector.op == "two") {
//    i = 2;
//  }
//  else {
//    i = 3;
//  }
  return i;
};
