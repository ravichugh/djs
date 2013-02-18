/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star    /*: Bool */ = "#extern";
var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

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

var replace = /*: {(and
        (v:: (this: Ref(~lBunch), replacement: Ref(lA)) / (lA: tyBunchArr) -> Top / sameExact )
        (v:: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact )
        (v:: (this: Ref(~lBunch))-> Top )
    )} */ "#extern";
Bunch.prototype.replace = replace;


var quest = /*: (Ref(~lQuery), Ref(~lNodes)) -> Ref(~lNodes) */ "#extern";

var parse_query = /*: (text: Str, id: Str) -> Ref(~lQuery) */ "#extern";

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

var id = /*: Str */ "#extern";

//----------------------------------------------------------------------------



var protect = function ()
/*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  reject_global(this);
  var b = this.___nodes___;
  /*: b lNodes */ "#thaw";
  var i /*: { Int | (>= v 0)} */ = 0;
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> sameType */ 
  for (i = 0; i < b.length; i += 1) {
    b[i]['___adsafe root___'] = '___adsafe root___';
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};

var q = function (text) 
/*: (this: Ref(~lBunch), Str) -> Ref(~lBunch) */
{
  reject_global(this);
  star = this.___star___;
  return new Bunch(quest(parse_query(string_check(text), id),
        this.___nodes___));
};

var remove = function () /*: (this: Ref(~lBunch)) -> Top */ {
  reject_global(this);
  this.replace();
};

