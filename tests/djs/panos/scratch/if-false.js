/*: (~lO:  { } > lObjPro) */ "#weak";
/*: (~lS:  Arr(Ref(~lO)) > lArrPro) */ "#weak";

var bar = function (b)
/*: (b: Ref(~lS)) ->Top */
{
  /*: b lS */ "#thaw";
  b.length;
  /*: b (~lS, thwd lS) */ "#freeze";

  if (false) {
    /*: b lS */ "#thaw";
    b.length;
    /*: b (~lS, thwd lS) */ "#freeze";
  }
};
