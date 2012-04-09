var beget = function (o) {
  function ctor() { return this; };
  ctor.prototype = o;
  return new ctor();
};

var herb = {
  name : "Herb",
  get_name : function() {
    return "Hi, I'm " + this.name;
  }
};

var henrietta = beget(herb);
henrietta.name = "Henrietta";
var s = henrietta.get_name();
s;

herb.get_name = function() { return 42; };
var i = henrietta.get_name();
i;
