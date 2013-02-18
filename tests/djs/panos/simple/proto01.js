/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

function Bunch(nodes)
/*: new (this:Ref, nodes: Ref(~lNodes)) / (this: Empty > lBunchProto, ~lBunch: frzn) ->
  Ref(~lBunch) / (~lBunch: frzn) */ {
  this.___nodes___ = nodes;
  this.___star___ = true;
  var self = this;
  /*: self (~lBunch,frzn) */ "#freeze";
  return self;
};


Bunch.prototype.getChecks = function () /*: (this: Ref(~lBunch)) -> Top */ { };
Bunch.prototype.getNames = function () /*: (this: Ref(~lBunch)) -> Top */ { };

var getCheck = function () /*: (this: Ref(~lBunch)) -> Top */ { var elts = this.getChecks(); };
var getName = function () /*: (this: Ref(~lBunch)) -> Top */ { var names = this.getNames(); };

//XXX: this does not work
//Bunch.prototype.getChecks = function () /*: (this: Ref(~lBunch)) -> Top */ { };
//var getCheck = function () /*: (this: Ref(~lBunch)) -> Top */ { var elts = this.getChecks(); };
//Bunch.prototype.getNames = function () /*: (this: Ref(~lBunch)) -> Top */ { };
//var getName = function () /*: (this: Ref(~lBunch)) -> Top */ { var names = this.getNames(); };
