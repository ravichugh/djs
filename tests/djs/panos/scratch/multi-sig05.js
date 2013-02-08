//Why is this not working? --> It works if you move var cond outside of the
//Array check

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
/*: tyBunchObj { "___nodes___": Ref(~lNodes), "___star___": Bool} > lObjPro */ "#define";
/*: tyBunchArr { Arr(Ref(~lBunch))|(packed v)} > lArrPro */ "#define";


var replace = function (replacement)
/*: {(and
        (v:: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact )
    )} */
{
  var b = this.___nodes___;
  if (isArray(replacement)) {
    /*: b lNodes */ "#thaw";
    b.length;
    var cond = true;
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
};
