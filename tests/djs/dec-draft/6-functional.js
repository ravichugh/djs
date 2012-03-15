
var mammal = function(priv) /*: ty_init_mammal */ {
  var x = /*: Lnew */ {};
  /*: Lnew */ x.get_name = function() /*: ty_get_name */ {
    return /*: Lpriv */ priv.name;
  };
  return x;
};

/*: #define ty_priv
    {(and ObjHas([v],"name",[Heap],lObject)
         (ObjSel([v],"name",[Heap],lObject) : Str))} */ '#define';

/*: #define ty_init_mammal
    [;Lnew,Lpriv;Heap]
        [[priv:Ref(Lpriv)]]
      / [Heap ++ lObject |-> (do:Top,lROOT), Lpriv |-> (dPriv:ty_priv,lObject)]
     -> Ref(Lnew)
      / [Heap ++ lObject |-> same, Lpriv |-> same,
         &priv |-> blah1:Ref(Lpriv),
         Lnew |-> (dNew:ty_mam, lObject)] */ '#define';

/*: #define ty_mam
    {(and (dom v {"get_name"})
          ((sel v "get_name") : ty_get_name))} */ '#define';

/*: #define ty_get_name
    [;Dummy1,Dummy2;Heap]
        [[this:Ref(Dummy1)]]
      / [Heap ++ Lpriv |-> (ePriv:ty_priv,lObject), &priv |-> blah:Ref(Lpriv)]
     -> {(= v ObjSel([ePriv],"name",[Heap],lObject))}
      / same */ '#define';

//////////////////////////////////////////////////////////////////////////////

var herbPriv = /*: lHerbPriv */ {name: "Herb"};
var herb     = /*: [;lHerb,lHerbPriv;] */ mammal(herbPriv);
var oldName  = /*: [;lHerb,lObject;] */ (herb.get_name)();

/*: {(= v "Herb")} */ oldName;

//////////////////////////////////////////////////////////////////////////////

 
/*: lHerbPriv */ herbPriv.name = "Herbert";
var newName   = /*: [;lHerb,lObject;] */ (herb.get_name)();

/*: {(= v "Herbert")} */ newName;

//////////////////////////////////////////////////////////////////////////////


var cat = function(priv2) /*: ty_init_cat */ {
  var obj = /*: [;Lnew,Lpriv;] */ mammal(priv2);
  /*: Lnew */ obj.purr = function() /*: ty_sound */ { return "purr"; };
  return obj;
};

/*: #define ty_init_cat
    [;Lnew,Lpriv;Heap]
        [[priv2:Ref(Lpriv)]]
      / [Heap ++ lObject |-> (do:Top,lROOT),
                 &mammal |-> blahMammal:ty_init_mammal,
                 Lpriv   |-> (dPriv:ty_priv,lObject)]
     -> Ref(Lnew)
      / [Heap ++ lObject |-> same,
                 Lpriv   |-> same,
                 &mammal |-> same,
                 &priv   |-> blah1:Ref(Lpriv),
                 Lnew    |-> (dNew:ty_cat, lObject)] */ '#define';

/*: #define ty_cat
    {(and (dom v {"get_name","purr"})
          ((sel v "get_name") : ty_get_name)
          ((sel v "purr") : ty_sound))} */ '#define';

/*: #define ty_sound [;L1,L2;] [[this:Ref(L1)]] -> Str */ '#define';

