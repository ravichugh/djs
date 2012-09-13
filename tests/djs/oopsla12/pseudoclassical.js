
/*: ty_mammal ::
       (this:Ref, name:Str) / (this: dThis:Empty > this.pro)
    -> Ref(this) / (this: {(= v (upd dThis "name" name))} > this.pro) */ '#type';

/*: ty_get_name ::
       (this:Ref) / (this: {Dict|(Str (objsel [v] "name" cur this.pro))} > this.pro)
    -> Str / same */ '#type';

function Mammal(name) /*: ty_mammal */ {
  this.name = name;
  return this;
};

Mammal.prototype.get_name = function() /*: ty_get_name */ {
  return "Hi, I'm " + this.name;
};

function Cat(name) /*: ty_mammal */ {
  this.name = name;
  return this;
};

Cat.prototype = new /*: lNewCatProto */ Mammal("__dummy__");

var henrietta = new /*: lHenrietta > lNewCatProto */ Cat("Henrietta");

var s = henrietta.get_name();

assert (typeof s === "string");

