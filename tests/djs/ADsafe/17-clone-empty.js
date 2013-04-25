var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyArr {Arr(Ref(~htmlElt))|(packed v)} > lArrPro */ "#define";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";


/*: tyNode  {
    getComputedStyle     : (this: Ref(~htmlElt), node : Ref(~htmlElt), str  : Str) -> Ref(~lStyle),
    currentStyle         : Ref(~lStyle),
    firstChild           : Ref(~htmlElt),
    nextSibling          : Ref(~htmlElt),
    parentNode           : Ref(~htmlElt),
    childNodes           : Ref(~htmlElts),
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
    blur                 : (this: Ref(~htmlElt)) -> Top,
    cloneNode             : (this: Ref(~htmlElt), deep:Bool) -> Ref(~htmlElt),
    getElementsByTagName : [;L;] (this: Ref(~htmlElt), name : Str) / () -> Ref(L) / (L: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
  } > lObjPro */ "#define";


var star    /*: Bool */         = "#extern";
var purge_event_handlers = /*: (node: Ref(~htmlElt)) -> Top */ "#extern";
var int_to_string /*: (Int) -> Str */ = "#extern";

// A Bunch is a container that holds zero or more dom nodes.
// It has many useful methods.

function Bunch(nodes)
  /*: new (this:Ref, nodes: Ref(~htmlElts)) / (this: Empty > lBunchProto, ~lBunch: frzn) ->
    Ref(~lBunch) / (~lBunch: frzn) */
{
  this.___nodes___ = nodes;
  /*: nodes htmlElts */ "#thaw";
  this.___star___ = star && nodes.length > 1;
  /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
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
       &a: Ref(lA), lA: {Arr(Ref(~lBunch))|(and (packed v) (= (len v) i0))} > lArrPro, &b: Ref(~htmlElts)) -> 
      (&i: {Int|(= v k0)}, &k:sameExact,
       &a: Ref(lA), lA: {Arr(Ref(~lBunch))|(and (packed v) (> (len v) 0))} > lArrPro, &b: sameType)
  */
  for (i = 0; i < k; i += 1) {
    var c  = /*: lC {Arr(Ref(~htmlElt))|(packed v)} */ [];
    /*: b htmlElts */ "#thaw";
    b.length;
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro,
          &c: Ref(lC), lC: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) -> sameType */
    for (j = 0; j < b.length && j < c.length; j += 1) {
      c.push(b[j].cloneNode(deep));
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  
    /*: c (~htmlElts,frzn) */ "#freeze";
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
    
  /*: nodes htmlElts */ "#thaw";
  var result = nodes.length;
  /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
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
    /*: b htmlElts */ "#thaw";
    var cond = i < b.length; 
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

    /*: (&b: Ref(~htmlElts), &cond: Bool) -> sameType */
    for (i = 0; cond; i += 1) {
      /*: b htmlElts */ "#thaw";
      if (i < b.length) {
        var bArr = /*: lBArr {Arr(Ref(~htmlElt))|(packed v)} */ [b[i]];
        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

        /*: bArr (~htmlElts, frzn) */ "#freeze";
        var bch = new Bunch(bArr);
        func(bch);
      }
      else {
        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
      }
    }
    return this;
  }
  error();
};

var value = /*: lArr { Arr(Str) | (packed v)} */ [];

var empty = function () 
//TODO: TCing succeeds for the two cases separately but not in the inconsistent 
//part and not fot the intersection type.
/* {(and
    (v :: (this: Ref(~lBunch)) / (&value: Ref(lArr), lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch)) / (&value: Ref(lObj), lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType)
    )} */
/* (this: Ref(~lBunch)) / (&value: Ref(lArr), lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType */
/*: (this: Ref(~lBunch)) / (&value: Ref(lObj), lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType */
{
  reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0,
      node /*: Ref(~htmlElt) */ = null;

  //PV: ugly hack to allow b.length as param to int_to_string
  var tmp_bl;

  if (isArray(value)) {
//    /*: b htmlElts */ "#thaw";
//    tmp_bl = b.length;
//    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//    if (value.length !== tmp_bl) {
//      error('ADsafe: Array length: ' + int_to_string(tmp_bl) + '-' +
//          int_to_string(value.length));
//    }
//    assert(/*: Ref(~htmlElts) */ (b));
//
//    /*: b htmlElts */ "#thaw";
//    assume(b != null);
//    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameExact */
//    for (i = 0; i < b.length; i += 1) {
//      node = b[i];
//      while (node.firstChild) {
//        purge_event_handlers(node);
//        node.removeChild(node.firstChild);
//      }
//    }
//    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  else {
    /*: b htmlElts */ "#thaw";
    b.length;
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      while (node.firstChild) {
        purge_event_handlers(node);
        node.removeChild(node.firstChild);
      }
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  return this;
};
