//Why is this not working? --> It works if you move var cond outside of the
//Array check

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
/*: tyBunchObj { "___nodes___": Ref(~lNodes), "___star___": Bool} > lObjPro */ "#define";
/*: tyBunchArr { Arr(Ref(~lBunch))|(packed v)} > lArrPro */ "#define";


var replace = function (replacement)
/*: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact */
{
  var b = this.___nodes___,
      rep /*: Ref(~lNodes) */ = null,
      cond /*: Bool */ = true,
      i  = 0;

  if (isArray(replacement)) {

    assert(false);
    /*: (&b: Ref(~lNodes), &cond: Bool, &i: {Int|(>= v 0)}) -> sameType */ 
    for (i = 0; i < replacement.length; i += 1) {
      if (i < replacement.length) {
        rep = replacement[i];
        rep = replacement[i].___nodes___;
        /*: rep lNodesRep */ "#thaw";
        rep.length;
        /*: rep (~lNodes, thwd lNodesRep) */ "#freeze";
      }
    }

  }
};


var bar = function() 
/*: () -> Top */ 
{
  var a = [];
  a[0];    
  var b = 1;
  b[0];    
};


