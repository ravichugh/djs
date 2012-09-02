
/*: #define ty_priv {Dict|(Str (objsel [v] "name" [Heap] lObjPro))} */ '#define';

/*: get_name :: [;Dummy1;Heap]
      [[this:Ref(Dummy1)]]
    / [Heap ++ Lpriv |-> (ePriv:ty_priv,lObjPro), &priv |-> __:Ref(Lpriv)]
   -> {(= v (objsel [ePriv] "name" [Heap] lObjPro))} / same */ '#type';

/*: mammal :: [;Lnew,Lpriv;Heap]
              [[priv:Ref(Lpriv)]]
            / [Heap ++ lObjPro |-> (do:Dict,lROOT), Lpriv |-> (dPriv:ty_priv,lObjPro)]
           -> Ref(Lnew) / [Heap ++ lObjPro |-> same, Lpriv |-> same,
                           &priv |-> _:Ref(Lpriv),
                           Lnew |-> (dNew:ty_mam, lObjPro)] */ '#type';

/*: ty_mam = {Dict|(and (dom v {"get_name"})
                        ((sel v "get_name") :: get_name))} */ '#type';

var mammal = function(priv) {
  var x = /*: Lnew */ {};
  x.get_name = function() {
    return priv.name;
  };
  return x;
};

var herbPriv = /*: lHerbPriv */ {name: "Herb"};
var herb     = /*: [;lHerb,lHerbPriv;] */ mammal(herbPriv);
var oldName  = herb.get_name();

assert (oldName === "Herb");

herbPriv.name = "Herbert";
var newName   = herb.get_name();

assert (newName === "Herbert");

/*: purr :: [;L1;] [[this:Ref(L1)]] -> Str */ '#type';

/*: ty_cat = {(and (= (tag v) "Dict") (dom v {"get_name","purr"})
                         ((sel v "get_name") :: get_name)
                         ((sel v "purr") :: purr))} */ '#type';

/*: cat :: [;Lnew,Lpriv;Heap]
           [[priv2:Ref(Lpriv)]] / [Heap ++ lObjPro |-> (do:Dict,lROOT),
                                   &mammal |-> _:mammal,
                                   Lpriv   |-> (dPriv:ty_priv,lObjPro)]
        -> Ref(Lnew) / [Heap ++ lObjPro |-> same, Lpriv |-> same, &mammal |-> same,
                                &priv   |-> _:Ref(Lpriv),
                                Lnew    |-> (dNew:ty_cat, lObjPro)] */ '#type';

var cat = function(priv2) {
  var obj = /*: [;Lnew,Lpriv;] */ mammal(priv2);
  obj.purr = function() { return "purr"; };
  return obj;
};

