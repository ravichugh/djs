
var make_dog = function(x) {
  x.bark = function() { return "bark"; };
};

var make_cat = function(x) {
  x.purr = function() { return "purr"; };
};

var hybrid = {};
make_dog(hybrid);
make_cat(hybrid);
var noise = hybrid.bark() + hybrid.purr();
/*: Str */ noise;

