
var make_dog = function(x) /*: ty_make_dog */ {
  /*: L1 L2 */ x.bark = function() /*: ty_sound */ { return "bark"; };
};

var make_cat = function(x) /*: ty_make_cat */ {
  /*: L1 L2 */ x.purr = function() /*: ty_sound */ { return "purr"; };
};

var hybrid = /*: l */ {};
/*: [;l,lObject;] */ make_dog(hybrid);
/*: [;l,lObject;] */ make_cat(hybrid);
var noise = /*: [;l,lObject;] */ (hybrid.bark)()
          ^ /*: [;l,lObject;] */ (hybrid.purr)();
/*: Str */ noise;


/*: #define ty_make_dog
    [;L1,L2;]
         [[x:Ref(L1)]]
       / [L1 |-> (dThis:Top, L2)]
      -> Top
       / [L1 |-> (dThis':{(and (eqmod v dThis {"bark"})
                               ((sel v "bark") :: ty_sound))}, L2)]
*/ '#define';

/*: #define ty_make_cat
    [;L1,L2;]
         [[x:Ref(L1)]]
       / [L1 |-> (dThis:Top, L2)]
      -> Top
       / [L1 |-> (dThis':{(and (eqmod v dThis {"purr"})
                               ((sel v "purr") :: ty_sound))}, L2)]
*/ '#define';

/*: #define ty_sound [;L1,L2;] [[this:Ref(L1)]] -> Str */ '#define';

