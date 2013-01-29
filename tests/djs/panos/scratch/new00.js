 
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

function Bunch(nodes)
/*: new (this:Ref, nodes: Ref(~lNodes)) / (this: Empty > lBunchProto, ~lBunch: frzn)
        -> Ref(~lBunch) / (~lBunch: frzn) */
{
  this.___nodes___ = nodes;
  /*: nodes lNodes */ "#thaw";
  this.___star___ = nodes.length > 1;
  /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
  var self = this;
  /*: self (~lBunch,frzn) */ "#freeze";
  return self;
};

