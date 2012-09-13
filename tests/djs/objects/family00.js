/*: #define nativeIn
    lObjPro |-> _:Top > lROOT, lFunPro |-> _:Top > lObjPro */ "#define";

/*: #define nativeOut
    lObjPro |-> same, lFunPro |-> same */ "#define";

/*: #define ty_beget [;LL1,LL2,LL3;]
        (o:Ref(LL2)) / (LL2 |-> dParent:Top > LL3, nativeIn)
     -> Ref(LL1) / (LL1 |-> dChild:{(= v empty)} > LL2, LL2 |-> same, nativeOut)
*/ '#define';

/*: #define ty_ctor [;Lnew,Lpro;]
        (this:Ref(Lnew)) / (Lnew |-> dThis:{(= v empty)} > Lpro)
     -> Ref(Lnew) / same */ '#define';

var beget = function (o) /*: ty_beget */ {
  function ctor() /*: new ty_ctor */ { return this; };
  ctor.prototype = o;
  return new /*: LL1 > LL2 */ ctor();
};

var parent = /*: lParent */ {"last": " Doe"};
var child = /*: [;lChild,lParent,lObjPro;] */ beget(parent);

assert ("last" in child == true);
assert (child.hasOwnProperty("last") == false);

