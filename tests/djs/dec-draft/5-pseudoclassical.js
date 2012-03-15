
/*: #define ty_mammal
    new [;Lthis,Lpro;]
        [[this:Ref(Lthis), name:Str]]
      / [Lthis |-> (dThis:{(= v empty)}, Lpro)]
     -> Ref(Lthis)
      / [Lthis |-> (dThis2:{(= v (upd dThis "name" name))}, Lpro)]
*/ '#define';

/*: #define ty_get_name
    [; Lthis,Lpro; H]
        [[this:Ref(Lthis)]]
      / [H ++ Lthis |-> (dThis:{
           (and ObjHas([v],"name",[H],Lpro)
               (ObjSel([v],"name",[H],Lpro) : Str))}, Lpro)]
     -> Str / same */ '#define';

function Mammal(name) /*: ty_mammal */ {
  /*: Lthis Lpro */ this.name = name;
  return this;
};

/*: &Mammal_proto */
(Mammal.prototype).get_name = function() /*: ty_get_name */ {
  return "Hi, I'm " ^ /*: Lthis Lpro */ this.name;
};

function Cat(name) /*: ty_mammal */ {
  /*: Lthis Lpro */ this.name = name;
  return this;
};

Cat.prototype = new /*: [;lCatPro,&Mammal_proto;] &Mammal_proto */
  Mammal("__dummy__");

var henrietta = new /*: [;lHenrietta,lCatPro;] lCatPro */
  Cat("Henrietta");

var s = /*: [;lHenrietta,lCatPro;] */ (henrietta.get_name)();

/*: Str */ s;

