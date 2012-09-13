
/*: beget :: [;LL1,LL2,LL3;]
    (Ref(LL2)) / (LL2: Top > LL3) -> Ref(LL1) / (LL1: Empty > LL2, LL2: same) */ '#type';

/*: ctor :: (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ '#type';

var beget = function (o) {
  function ctor() { return this; };
  ctor.prototype = o;
  return new /*: LL1 > LL2 */ ctor();
};

/*: get_name :: (this:Ref) / (this: {Dict|(Str (objsel [v] "name" cur this.pro))} > this.pro)
             -> Str / same */ '#type';

var herb = /*: lHerb */ {
  name : "Herb",
  get_name : function() {
    return "Hi, I'm " + this.name;
  }
};

var henrietta = /*: [;lHenrietta,lHerb,lObjPro;] */ beget(herb);
henrietta.name = "Henrietta";
var s = henrietta.get_name();
assert (typeof s === "string");

herb.get_name = function() /*: (this:Top) -> Int */ { return 42; };
var i = henrietta.get_name();
assert (typeof i === "number");
