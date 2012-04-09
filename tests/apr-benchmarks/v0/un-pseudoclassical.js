function Mammal(name) {
  this.name = name;
  return this;
};

Mammal.prototype.get_name = function() {
  return "Hi, I'm " + this.name;
};

function Cat(name) {
  this.name = name;
  return this;
};

Cat.prototype = new Mammal("__dummy__");

var henrietta = new Cat("Henrietta");

var s = henrietta.get_name();

s;

