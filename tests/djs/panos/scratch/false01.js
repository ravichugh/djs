
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var append = function (a, b) 
/*: (a: Ref(~lBunch), b: Ref(~htmlElts)) -> Top*/
{

  /*: b htmlElts */ "#thaw";
  assume(b!=null);
  b.length === 0;
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

  if (isArray(a)) {

    /*: b htmlElts */ "#thaw";
    assume(b!=null);
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }


};

