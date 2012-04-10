
var mammal = function(priv) {
  var x = {};
  x.get_name = function() {
    return priv.name;
  };
  return x;
};

var herbPriv = {name: "Herb"};
var herb     = mammal(herbPriv);
var oldName  = herb.get_name();

oldName;

 
herbPriv.name = "Herbert";
var newName   = herb.get_name();

newName;


var cat = function(priv2) {
  var obj = mammal(priv2);
  obj.purr = function() { return "purr"; };
  return obj;
};

