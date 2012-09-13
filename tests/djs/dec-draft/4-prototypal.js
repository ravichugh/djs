
/*: #define nativeIn lObjPro |-> _:Top > lROOT, lFunPro |-> _:Top > lObjPro */ "#define";

/*: #define nativeOut lObjPro |-> same, lFunPro |-> same */ "#define";

/*: #define ty_beget
    [;LL1,LL2,LL3;]
        (o:Ref(LL2)) / (LL2 |-> dParent:Top > LL3, nativeIn)
     -> Ref(LL1) / (LL1 |-> dChild:{(= v empty)} > LL2, LL2 |-> same, nativeOut)
*/ '#define';

/*: #define ty_ctor
    new [;Lnew,Lpro;]
        (this:Ref(Lnew)) / (Lnew |-> dThis:{(= v empty)} > Lpro)
     -> Ref(Lnew) / same */ '#define';

var beget = function (o) /*: ty_beget */ {
  function ctor() /*: ty_ctor */ { return this; }; // TODO upper case letter
  ctor.prototype = o;
  return new /*: LL1 > LL2 */ ctor();
};

/*: #define ty_get_name
    [; Lthis,Lpro; H]
        (this:Ref(Lthis))
      / H + (Lthis |-> dThis:{Dict|
           (and (objhas [v] "name" H Lpro)
                (Str (objsel [v] "name" H Lpro)))} > Lpro)
     -> Str / same */ '#define';

var herb = /*: lHerb */ {
  name : "Herb",
  get_name : function() /*: ty_get_name */ {
    return "Hi, I'm " + this.name;
  }
};

var henrietta = /*: [;lHenrietta,lHerb,lObjPro;] */ beget(herb);
henrietta.name = "Henrietta";
var s = henrietta.get_name();
assert (typeof s == "string");

/*: #define ty_get_name_2
    [; Lthis; ] (this:Ref(Lthis)) -> Int */ '#define';

herb.get_name = function() /*: ty_get_name_2 */ { return 42; };
var i = henrietta.get_name();
assert (/*: Int */ i);
