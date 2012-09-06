
/*: #define nativeIn lObjPro: Top > lROOT, lFunPro: Top > lObjPro */ "#define";

/*: #define nativeOut lObjPro: same, lFunPro: same */ "#define";

/*: beget :: [;LL1,LL2,LL3;]
        (Ref(LL2)) / (LL2: Top > LL3, nativeIn)
     -> Ref(LL1) / (LL1: Empty > LL2, LL2: same, nativeOut) */ '#type';

/*: ctor :: [;Lnew,Lpro;]
        (this:Ref(Lnew)) / (Lnew: Empty > Lpro) -> Ref(Lnew) / same */ '#type';

var beget = function (o) {
  function ctor() { return this; };
  ctor.prototype = o;
  return new /*: [;LL1,LL2;] LL2 */ ctor();
};

/*: #define ty_get_name [; Lthis,Lpro; H]
        (this:Ref(Lthis)) / H + (Lthis: {Dict|(Str (objsel [v] "name" H Lpro))} > Lpro)
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
assert (typeof s === "string");

/*: #define ty_get_name_2 [; Lthis; ] (this:Ref(Lthis)) -> Int */ '#define';

herb.get_name = function() /*: ty_get_name_2 */ { return 42; };
var i = henrietta.get_name();
assert (typeof i === "number");
