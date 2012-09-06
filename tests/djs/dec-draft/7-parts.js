
var make_dog = function(x) /*: ty_make_dog */ {
  x.bark = function() /*: ty_sound */ { return "bark"; };
};

var make_cat = function(x) /*: ty_make_cat */ {
  x.purr = function() /*: ty_sound */ { return "purr"; };
};

var hybrid = /*: l */ {};
make_dog(hybrid);
make_cat(hybrid);
var noise = hybrid.bark() + hybrid.purr();
assert (/*: Str */ noise);


/*: #define ty_make_dog
    [;L1,L2;] (x:Ref(L1)) / (L1 |-> dThis:Dict > L2)
      -> Top / (L1 |-> dThis':{(and (eqmod v dThis {"bark"})
                                    ((sel v "bark") :: ty_sound))} > L2)
*/ '#define';

/*: #define ty_make_cat
    [;L1,L2;] (x:Ref(L1)) / (L1 |-> dThis:Dict > L2)
      -> Top / (L1 |-> dThis':{(and (eqmod v dThis {"purr"})
                                    ((sel v "purr") :: ty_sound))} > L2)
*/ '#define';

/*: #define ty_sound [;L1;] (this:Ref(L1)) -> Str */ '#define';
