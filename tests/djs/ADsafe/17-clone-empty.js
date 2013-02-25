var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyArr {Arr(Ref(~lNode))|(packed v)} > lArrPro */ "#define";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";


/*: tyNode  {
    getComputedStyle     : (this: Ref(~lNode), node : Ref(~lNode), str  : Str) -> Ref(~lStyle),
    currentStyle         : Ref(~lStyle),
    firstChild           : Ref(~lNode),
    nextSibling          : Ref(~lNode),
    parentNode           : Ref(~lNode),
    childNodes           : Ref(~lNodes),
    change               : Ref(~lEvent),
    "___ on ___"         : Ref(~lEvent),
    "___adsafe root___"  : Bool,
    tagName              : Str,
    className            : Str,
    name                 : Str,
    nodeName             : Str,
    nodeValue            : Str,
    disabled             : Bool,
    checked              : Bool,
    fire                 : (NotUndef) -> Top,
    blur                 : (this: Ref(~lNode)) -> Top,
    cloneNode             : (this: Ref(~lNode), deep:Bool) -> Ref(~lNode),
    getElementsByTagName : [;L;] (this: Ref(~lNode), name : Str) / () -> Ref(L) / (L: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
  } > lObjPro */ "#define";


var star    /*: Bool */         = "#extern";
var purge_event_handlers = /*: (node: Ref(~lNode)) -> Top */ "#extern";
var int_to_string /*: (Int) -> Str */ = "#extern";

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


var clone =  function (deep, n) 
/*: (this: Ref(~lBunch), deep:Bool, n: {Int|(>= v 0)}) -> 
  {(ite (truthy n) (v::Ref(~lBunches)) (v::Ref(~lBunch)))} */
{
  /*: this lBunch */ "#thaw";
  var a = /*: lA {Arr(Ref(~lBunch))|(and (packed v) (= (len v) 0))} */ [];
  var b = this.___nodes___;    
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var i /*: { Int | (>= v 0)} */ = 0,
      j /*: { Int | (>= v 0)} */ = 0,
      k = n || 1;

  /*: (&i:i0: {Int|(and (>= v 0) (<= v k0))}, &k:k0:{Int|(> v 0)},
       &a: Ref(lA), lA: {Arr(Ref(~lBunch))|(and (packed v) (= (len v) i0))} > lArrPro, &b: Ref(~lNodes)) -> 
      (&i: {Int|(= v k0)}, &k:sameExact,
       &a: Ref(lA), lA: {Arr(Ref(~lBunch))|(and (packed v) (> (len v) 0))} > lArrPro, &b: sameType)
  */
  for (i = 0; i < k; i += 1) {
    var c  = /*: lC {Arr(Ref(~lNode))|(packed v)} */ [];
    /*: b lNodes */ "#thaw";
    b.length;
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro,
          &c: Ref(lC), lC: {Arr(Ref(~lNode))|(packed v)} > lArrPro) -> sameType */
    for (j = 0; j < b.length && j < c.length; j += 1) {
      c.push(b[j].cloneNode(deep));
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  
    /*: c (~lNodes,frzn) */ "#freeze";
    a.push(new Bunch(c));
  }
  if (n) {
    /*: a (~lBunches,frzn) */ "#freeze";
    return a;
  }
  else {
    return a[0];
  }
//  return n ? a : a[0];    //PV: original code
};


var count = function () 
/*: (this: Ref(~lBunch)) -> Int */
{
  reject_global(this);

  /*: this lBunch */ "#thaw";
  var nodes =  this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
    
  /*: nodes lNodes */ "#thaw";
  var result = nodes.length;
  /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
  return result;
};

  
var each = function (func) 
/*: (this: Ref(~lBunch), func: (Ref(~lBunch)) -> Top) -> Top */
{
  reject_global(this);

  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0;

  if (typeof func === 'function') {
    /*: b lNodes */ "#thaw";
    var cond = i < b.length; 
    /*: b (~lNodes, thwd lNodes) */ "#freeze";

    /*: (&b: Ref(~lNodes), &cond: Bool) -> sameType */
    for (i = 0; cond; i += 1) {
      /*: b lNodes */ "#thaw";
      if (i < b.length) {
        var bArr = /*: lBArr {Arr(Ref(~lNode))|(packed v)} */ [b[i]];
        /*: b (~lNodes, thwd lNodes) */ "#freeze";

        /*: bArr (~lNodes, frzn) */ "#freeze";
        var bch = new Bunch(bArr);
        func(bch);
      }
      else {
        /*: b (~lNodes, thwd lNodes) */ "#freeze";
      }
    }
    return this;
  }
  error();
};

var value = /*: lArr { Arr(Str) | (packed v)} */ [];

var empty = function () 
/*: {(and
    (v :: (this: Ref(~lBunch)) / (&value: Ref(lArr), lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch)) / (&value: Ref(lObj), lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType)
    )} */
{
  reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0,
      node /*: Ref(~lNode) */ = null;

  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    if (value.length !== b.length) {
//TODO      
//      error('ADsafe: Array length: ' + int_to_string(b.length) + '-' +
//          int_to_string(value.length));
    }
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      node.firstChild;
      /*: (&node: Ref(~lNode)) -> sameType */
      while (node.firstChild) {
        purge_event_handlers(node);
        node.removeChild(node.firstChild);
      }
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  } else {
    /*: b lNodes */ "#thaw";
    b.length;
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      while (node.firstChild) {
        purge_event_handlers(node);
        node.removeChild(node.firstChild);
      }
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};
