
var mammal = function(priv) /*: ty_init_mammal */ {
  var x = /*: Lnew */ {};
  x.get_name = function() /*: ty_get_name */ {
    return priv.name;
  };
  return x;
};

/*: ty_priv {Dict|(Str (sel v "name"))} */ '#define';

/*: ty_init_mammal [;Lnew,Lpriv]
        (priv:Ref(Lpriv)) / (Lpriv: dPriv:ty_priv > lObjPro)
     -> Ref(Lnew) / (Lpriv: same, &priv: blah1:Ref(Lpriv),
                     Lnew: dNew:ty_mam > lObjPro) */ '#define';

/*: ty_mam {get_name: ty_get_name, _:Bot} */ '#define';

/*: ty_get_name
        (this:Top) / (Lpriv: ePriv:ty_priv > lObjPro, &priv: blah:Ref(Lpriv))
     -> {(= v (sel ePriv "name"))} / same */ '#define';

//////////////////////////////////////////////////////////////////////////////

var herbPriv = /*: lHerbPriv */ {name: "Herb"};
var herb     = /*: [;lHerb,lHerbPriv;] */ mammal(herbPriv);
var oldName  = herb.get_name();

assert (oldName == "Herb");

//////////////////////////////////////////////////////////////////////////////

 
herbPriv.name = "Herbert";
var newName   = herb.get_name();

assert (newName == "Herbert");

//////////////////////////////////////////////////////////////////////////////


var cat = function(priv2) /*: ty_init_cat */ {
  var obj = /*: [;Lnew,Lpriv;] */ mammal(priv2);
  obj.purr = function() /*: ty_sound */ { return "purr"; };
  return obj;
};

/*: ty_init_cat [;Lnew,Lpriv]
        (priv2:Ref(Lpriv)) / (Lpriv: dPriv:ty_priv > lObjPro)
     -> Ref(Lnew) / (Lpriv: same, &priv: blah1:Ref(Lpriv),
                     Lnew: dNew:ty_cat > lObjPro) */ '#define';

/*: ty_cat {purr: ty_sound, get_name: ty_get_name, _:Bot} */ '#define';

/*: ty_sound (this:Top) -> Str */ '#define';

