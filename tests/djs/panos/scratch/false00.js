/*: (~a: {                   } > lObjPro) */ "#weak";
/*: (~b: {Arr(Top)|(packed v)} > lArrPro) */ "#weak";

var append = function (a, b) 
/*: (a: Ref(~a), b: Ref(~b)) -> Top */
{

  /*: b lb */ "#thaw";
  assume(b!=null);
  b.length === 0;
  /*: b (~b, thwd lb) */ "#freeze";

  if (isArray(a)) {

    /*: b lb */ "#thaw";
    assume(b!=null);
    /*: b (~b, thwd lb) */ "#freeze";
  }

};

