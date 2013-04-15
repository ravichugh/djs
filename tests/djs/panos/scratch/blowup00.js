
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
var error = /*: (message: Str)  -> Top */ "#extern";

/*: (~lD : {} > lObjPro) */ "#weak";

var foo = function(i, d, a)
/*: (i:Int, d: Ref(~lD), a: Ref) / (a: Arr(Ref(~lD)) > lArrPro)-> Top / sameType */
{
  if (i == 0) {
    error("a");
  }

  if (i > 1) {
    /*: d lD */ "#thaw";
    d = { };
    /*: d (~lD, thwd lD) */ "#freeze";
  }
  else if (i > 2) {
    if (i > 4) {
      /*: d lD */ "#thaw";
      d = { };
      /*: d (~lD, thwd lD) */ "#freeze";
    }
    else {
      /*: d lD */ "#thaw";
      d = { };
      /*: d (~lD, thwd lD) */ "#freeze";
    }
  }
//  else if (i > 3) {
//    /*: d lD */ "#thaw";
//    d = { };
//    /*: d (~lD, thwd lD) */ "#freeze";
//
//  }
//  else if (i > 4) {
//
//    /*: d lD */ "#thaw";
//    d = { op: '1'};
//    /*: d (~lD, thwd lD) */ "#freeze";
//  }
//  else {
//  
//    /*: d lD */ "#thaw";
//    d = { };
//    /*: d (~lD, thwd lD) */ "#freeze";
//  
//  }
    
  a.push(d);

};
