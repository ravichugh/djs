
var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyArr {Arr(Ref(~lNode))|(packed v)} > lArrPro */ "#define";

var ephemeral /*: Ref(~lBunch) */ = "#extern";
var star    /*: Bool */         = "#extern";

// A Bunch is a container that holds zero or more dom nodes.
// It has many useful methods.

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

var remove = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
Bunch.prototype.remove = remove;

var reject_global = /*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

// -----------------------------------------------------------------------------------

var enable = function (enable) 
/*: {(and
    (v :: (this: Ref(~lBunch), enable: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), enable: Ref(lObj)) / (lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType))} */
{
  reject_global(this);
 
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0,
      node /*: Ref(~lNode) */ = null;

  if (isArray(enable)) {
    /*: b lNodes */ "#thaw";
    if (enable.length !== b.length) {
//TODO      
      error('ADsafe: Array length: ... ' );
      //error('ADsafe: Array length: ' + b.length + '-' +
      //    enable.length);
    }
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        node.disabled = !enable[i];
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  } else {
    /*: b lNodes */ "#thaw";
    b.length;
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        node.disabled = !enable;
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};

var ephemeral_ = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  reject_global(this);
  if (ephemeral) {
    ephemeral.remove();
  }
  ephemeral = this;
  return this;
};



var explode = function () 
/*: [;L;] (this: Ref(~lBunch)) / () -> Ref(L) / (L: Arr(Ref(~lBunch)) > lArrPro) */
{
  reject_global(this);
  var a = /*: L {Arr(Ref(~lBunch))|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0;

  /*: (&b: Ref(~lNodes), &a: Ref(L), L: Arr(Ref(~lBunch)) > lArrPro) -> sameType */
  for (i = 0; true; i += 1) {
    /*: b lNodes */ "#thaw";
    if (i < b.length) {
      var bArr = /*: lBArr {Arr(Ref(~lNode))|(packed v)} */  [b[i]];
      /*: b (~lNodes, thwd lNodes) */ "#freeze";
      /*: bArr (~lNodes, frzn) */ "#freeze";
      a[i] =  new Bunch(bArr);
    }
    else{
      /*: b (~lNodes, thwd lNodes) */ "#freeze";
    }
  }
  return a;
};

