
/*: #define ty_sound (this:Top) -> Str */ '#define';

/*: ty_make_dog :: (x:Ref) / (x: dThis:Dict > x.pro)
    -> Top / (x: {(and (eqmod v dThis {"bark"})
                       ((sel v "bark") :: ty_sound))} > x.pro) */ '#type';

/*: ty_make_cat :: (x:Ref) / (x: dThis:Dict > x.pro)
    -> Top / (x: {(and (eqmod v dThis {"purr"})
                       ((sel v "purr") :: ty_sound))} > x.pro) */ '#type';

var make_dog = function(x) /*: ty_make_dog */ {
  x.bark = function() /*: ty_sound */ { return "bark"; };
};

var make_cat = function(x) /*: ty_make_cat */ {
  x.purr = function() /*: ty_sound */ { return "purr"; };
};

var hybrid = {};
make_dog(hybrid);
make_cat(hybrid);
var noise = hybrid.bark() + hybrid.purr();
assert (typeof noise == "string");

