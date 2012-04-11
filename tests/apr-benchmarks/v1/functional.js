
var mammal = function(priv) /*: ty_init_mammal */ {
  var x = /*: Lnew */ {};
  x.get_name = function() /*: ty_get_name */ {
    return priv.name;
  };
  return x;
};

/*: #define ty_priv {Dict|(objsel [v] "name" [Heap] lObjectProto : Str)} */ '#define';

/*: #define ty_init_mammal [;Lnew,Lpriv;Heap]
      [[priv:Ref(Lpriv)]]
    / [Heap ++ lObjectProto |-> (do:Dict,lROOT), Lpriv |-> (dPriv:ty_priv,lObjectProto)]
   -> Ref(Lnew) / [Heap ++ lObjectProto |-> same, Lpriv |-> same,
                   &priv |-> _:Ref(Lpriv),
                   Lnew |-> (dNew:ty_mam, lObjectProto)] */ '#define';

/*: #define ty_mam {Dict|(and (dom v {"get_name"})
                              ((sel v "get_name") : ty_get_name))} */ '#define';

/*: #define ty_get_name [;Dummy1;Heap]
      [[this:Ref(Dummy1)]]
    / [Heap ++ Lpriv |-> (ePriv:ty_priv,lObjectProto), &priv |-> _:Ref(Lpriv)]
   -> {(= v (objsel [ePriv] "name" [Heap] lObjectProto))} / same */ '#define';

var herbPriv = /*: lHerbPriv */ {name: "Herb"};
var herb     = /*: [;lHerb,lHerbPriv;] */ mammal(herbPriv);
var oldName  = herb.get_name();

assert (oldName === "Herb");

herbPriv.name = "Herbert";
var newName   = herb.get_name();

assert (newName === "Herbert");


var cat = function(priv2) /*: ty_init_cat */ {
  var obj = /*: [;Lnew,Lpriv;] */ mammal(priv2);
  obj.purr = function() /*: ty_sound */ { return "purr"; };
  return obj;
};

/*: #define ty_init_cat [;Lnew,Lpriv;Heap]
        [[priv2:Ref(Lpriv)]] / [Heap ++ lObjectProto |-> (do:Dict,lROOT),
                                &mammal |-> _:ty_init_mammal,
                                Lpriv   |-> (dPriv:ty_priv,lObjectProto)]
     -> Ref(Lnew) / [Heap ++ lObjectProto |-> same, Lpriv |-> same, &mammal |-> same,
                             &priv   |-> _:Ref(Lpriv),
                             Lnew    |-> (dNew:ty_cat, lObjectProto)] */ '#define';

/*: #define ty_cat {(and (= (tag v) "Dict") (dom v {"get_name","purr"})
                         ((sel v "get_name") : ty_get_name)
                         ((sel v "purr") : ty_sound))} */ '#define';

/*: #define ty_sound [;L1;] [[this:Ref(L1)]] -> Str */ '#define';

