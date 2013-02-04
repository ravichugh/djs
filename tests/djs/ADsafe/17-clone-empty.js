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


var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";
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




var clone =  function (deep, n) 
/*: (this: Ref(~lBunch), deep:Bool, n: Num) -> Top */
{
  /*: this lBunch */ "#thaw";
  var a = [],
      b = this.___nodes___,     
//      c,
      c /*: Ref(~lNodes) */ = null,
      i /*: { Int | (>= v 0)} */ = 0,
      j /*: { Int | (>= v 0)} */ = 0,
      k = n || 1;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

//XXX: Will probably multiple strong locations for the same weak location
//  for (i = 0; i < k; i += 1) {
//    for (j = 0; j < b.length; j += 1) {
//      c.push(b[j].cloneNode(deep));
//    }
//    a.push(new Bunch(c));
//  }
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
    /*: b lNodes */ "#thaw";
    b.length;        //XXX: WHY?????? 

    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {

      assert(/*: Ref(~lNode) */  (b[i]));
      var bArr = /*: lBArg Arr(Ref(~lNode)) */ [b[i]];
//XXX: Will probably multiple strong locations for the same weak location
//      var bch = new Bunch(bArr);
//      func(bch);

    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
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
//      error('ADsafe: Array length: ' + b.length + '-' +
//          value.length);
    }
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      assert(/*: Ref(~lNode) */  (node.firstChild));

//      /*: (&node: Ref(lNode), lNode: tyNode) -> sameType */
//      while (node.firstChild) {
//        purge_event_handlers(node);
//        node.removeChild(node.firstChild);
//      }
      
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
      assert(/*: Ref(~lNode) */  (node.firstChild));
//      while (node.firstChild) {
//        purge_event_handlers(node);
//        node.removeChild(node.firstChild);
//      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};
