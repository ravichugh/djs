/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyArr {Arr(Ref(~lNode))|(packed v)} > lArrPro */ "#define";


/*: tyNode  {
    getComputedStyle     : (this: Ref(~lNode), node : Ref(~lNode), str  : Str) -> Ref(~lCCSStyle),
    currentStyle         : Ref(~lCCSStyle),
    firstChild           : Ref(~lNode),
    nextSibling          : Ref(~lNode),
    parentNode           : Ref(~lNode),
    childNodes           : Ref(~lNList),
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


var error = /*: (message: Str)  -> {FLS}  */ "#extern";
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
//TODO: make more precise type
/*: (this: Ref(~lBunch), deep:Bool, n: Int) -> {(ite (truthy n) TRU TRU)} */
{
  /*: this lBunch */ "#thaw";
  var a = /*: lA {Arr(Ref(~lBunch))|(packed v)} */ [];
  var b = this.___nodes___;    
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var i /*: { Int | (>= v 0)} */ = 0,
      j /*: { Int | (>= v 0)} */ = 0,
      k = n || 1;

  /*: (&a: Ref(lA), lA: {Arr(Ref(~lBunch))|(packed v)} > lArrPro
       ,&b: Ref(~lNodes)
      ) -> sameType */
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
  return n ? a : a[0];
};


var count = function () 
/*: (this: Ref(~lBunch)) -> Int */
{
  //reject_global(this);

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
  //reject_global(this);

  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0;

  if (typeof func === 'function') {

    /*: (&b: Ref(~lNodes)) -> sameType */
    for (i = 0; true; i += 1) {
      /*: b lNodes */ "#thaw";
       
      if (i < b.length) {
        assert(/*: Ref(~lNode) */  (b[i]));
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
  error("default");
};

var value = /*: lArr { Arr(Str) | (packed v)} */ [];

var empty = function () 
/*: {(and
    (v :: (this: Ref(~lBunch)) / (&value: Ref(lArr), lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch)) / (&value: Ref(lObj), lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType)
    )} */
{
  //reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0,
      node /*: Ref(~lNode) */ = null;

  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    if (value.length !== b.length) {
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
