var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star          /*: Bool */ = "#extern";
function Bunch(nodes)
  /*: new (this:Ref, nodes: Ref(~lNodes)) / (this: Empty > lBunchProto) -> Ref(~lBunch) / () */
{
  this.___nodes___ = nodes;
  /*: nodes lNodes */ "#thaw";
  this.___star___ = star && nodes.length > 1;
  /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
  star = false;
  var self = this;
  /*: self (~lBunch,frzn) */ "#freeze";
  return self;      //PV: added return
};

//PV: ~lBunch will be thawed everytime reject_global is called
var reject_global = function(that) 
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */
{
  if (that.window) {
    return error();
  }
};

var focus = function () /*: (this: Ref(~lBunch)) -> Top */ {
  /*: this lBunch */ "#thaw";
  assume(this != null);
  reject_global(this);
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
};
