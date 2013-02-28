var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
var document  = /*: Ref(~lDocument) */ "#extern";
var allow_focus = /*: Bool */ "#extern";
var has_focus /*: Top */ = "#extern";


var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var star    /*: Bool */         = "#extern";

function Bunch(nodes)
  /*: new (this:Ref, nodes: Ref(~lNodes)) / (this: Empty > lBunchProto, ~lBunch: frzn) ->
    Ref(~lBunch) / (~lBunch: frzn) */
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



var focus = function focus_rec() 
/*: (this: Ref(~lBunch)) -> Top */
{
  reject_global(this);
  var b = this.___nodes___;
  /*: b lNodes */ "#thaw";
  b.l;
  if (b.length > 0 && allow_focus) {
    var node = b[0];
    has_focus = node.focus();
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
    return this;
  }
  //PV: had to put else branch
  else {
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
    error();
  }
};

var fragment = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  reject_global(this);
  var arr = /*: lArr {Arr(Ref(~lNode))|(packed v)} */ [document.createDocumentFragment()];
  /*: arr (~lNodes, frzn) */ "#freeze";
  return new Bunch(arr);
};
