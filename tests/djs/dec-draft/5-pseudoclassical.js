
/*: #define ty_mammal
    new [;Lthis,Lpro;]
        (this:Ref(Lthis), name:Str)
      / (Lthis |-> dThis:{(= v empty)} > Lpro)
     -> Ref(Lthis)
      / (Lthis |-> dThis2:{(= v (upd dThis "name" name))} > Lpro)
*/ '#define';

/*: #define ty_get_name
    [; Lthis,Lpro; H]
        (this:Ref(Lthis))
      / H + (Lthis |-> dThis:{Dict|
           (and (objhas [v] "name" H Lpro)
                (Str (objsel [v] "name" H Lpro)))} > Lpro)
     -> Str / same */ '#define';

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

Cat.prototype = new /*: lNewCatPro > lMammalProto */
  Mammal("__dummy__");

var henrietta = new /*: lHenrietta > lNewCatPro */
  Cat("Henrietta");

var s = henrietta.get_name();

assert (/*: Str */ s);

