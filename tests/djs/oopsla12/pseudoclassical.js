
/*: #define ty_mammal [;Lthis,Lpro;]
        [[this:Ref(Lthis), name:Str]] / [Lthis |-> (dThis:Empty, Lpro)]
     -> Ref(Lthis) / [Lthis |-> (dThis2:{(= v (upd dThis "name" name))}, Lpro)]
*/ '#define';

/*: #define ty_get_name [; Lthis,Lpro; H]
        [[this:Ref(Lthis)]]
      / [H ++ Lthis |-> (dThis:{Dict|(objsel [v] "name" [H] Lpro : Str)}, Lpro)]
     -> Str / same */ '#define';

function Mammal(name) /*: new ty_mammal */ {
  this.name = name;
  return this;
};

Mammal.prototype.get_name = function() /*: ty_get_name */ {
  return "Hi, I'm " + this.name;
};

function Cat(name) /*: new ty_mammal */ {
  this.name = name;
  return this;
};

Cat.prototype = new /*: [;lCatPro,lMammalProto;] lMammalProto */ Mammal("__dummy__");

var henrietta = new /*: [;lHenrietta,lCatPro;] lCatPro */ Cat("Henrietta");

var s = henrietta.get_name();

assert (typeof s === "string");

