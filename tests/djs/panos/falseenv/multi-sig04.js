/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
/*: tyBunchObj { "___nodes___": Ref(~htmlElts), "___star___": Bool} > lObjPro */ "#define";
/*: tyBunchArr { Arr(Ref(~lBunch))|(packed v)} > lArrPro */ "#define";

var replace = function (replacement)
/*: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact */
//WORKS WITH THIS NEXT TYPE
/* (this: Ref(~lBunch), replacement: Ref(lA)) / (lA: tyBunchArr) -> Top / sameExact */
{
  var b = this.___nodes___,
      rep /*: Ref(~htmlElts) */ = null,
      i /*: {Int|(>= v 0)} */  = 0;

  if (isArray(replacement)) {

    //assert(false);
    /*: (&b: Ref(~htmlElts)) -> sameType */ 
    for (i = 0; i < replacement.length; i += 1) {
      if (i < replacement.length) {
        rep = replacement[i];
        rep = replacement[i].___nodes___;
      }
    }

  }
};
