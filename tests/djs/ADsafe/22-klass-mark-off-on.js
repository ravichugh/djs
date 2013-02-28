var error = /*: {( and 
              (v:: (message: Str)  -> { FLS })
              (v:: ()  -> { FLS })              
              )} */ "#extern";
var dom_event = /*: (this: Ref(~lEvent), Ref(~lEvent))-> Top */ "#extern";

//TODO: Using an imprecise type for "owns"
var owns = 
/* (object: Ref, string: Str) / (object: d: Dict (* {Dict|(not (has v "hasOwnProperty"))} *) > lObjPro) -> 
    { (implies (= v true) (has d {string}))} / sameType */ 
/*: (object: Top, string: Str) -> Bool */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyEvent {
  altKey          : Bool,
  bubble          : (this: Ref(~lEvent))-> Top,
  cancelBubble    : Bool,
  ctrlKey         : Bool,
  key             : Str, 
  preventDefault  : (this: Ref(~lEvent)) -> Top,
  shiftKey        : Bool,
  srcElement      : Ref(~lNode),
  stopPropagation : (this: Ref(~lEvent))-> Top,
  target          : Ref(~lNode),    (* could also be Ref(~lEventTarget) *)
  that            : Ref(~lBunch),
  type_           : Str,
  _               : Bot
} */ "#define";


var String =  /*: (Top) -> Str */ "#extern";

var allow_focus /*: Bool */ = "#extern";
var star    /*: Bool */         = "#extern";
var the_range /*: Ref(~lRange) */  = "#extern";

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

var class_ = /*: {(and
      (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
      (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch) ) 
      )} */ "#extern";

Bunch.prototype['class'] = class_;


var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var int_to_string /*: (Int) -> Str */ = "#extern";

// -----------------------------------------------------------------------------------

var klass = function (value) /*: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch) */ {
  return this['class'](value);
};

var mark = function (value)
/*: {(and
    (v :: (this: Ref(~lBunch), value: Ref(lArr)) 
      / (lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch)) )} */
{
  reject_global(this);
  var b = this.___nodes___, node /*: Ref(~lNode) */ = null;
  var i /*: {Int | (>= v 0)}*/ = 0;
  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    if (value.length !== b.length) {
      error('ADsafe: Array length: ' /*+ int_to_string(b.length) + '-' +
         int_to_string(value.length)*/);
    }
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        node['_adsafe mark_'] = String(value[i]);
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  } 
  else {
    /*: b lNodes */ "#thaw";
    b.l;
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        node['_adsafe mark_'] = String(value);
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};

var off = function (type_) /*: (this: Ref(~lBunch), type_:Top) -> Ref(~lBunch) */ {
  reject_global(this);
  var b = this.___nodes___, 
      node /*: Ref(~lNode) */ = null;
  var i /*: {Int | (>= v 0)}*/ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    if (typeof type_ === 'string') {
      var e = node['___ on ___'];
      if (typeof e) {
        assume(typeof e[type_] === 'object');
        e[type_] = null;
      }
    } else {
      node['___ on ___'] = null;
    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};

var on = function (type_, func) 
/*: (this: Ref(~lBunch), type_:Top, func: Top) -> Ref(~lBunch) */ {
  reject_global(this);
  if (typeof type_ !== 'string' || typeof func !== 'function') {
    error();
  }
  assert(/*: {(= (tag v) "function")} */ (func));

  var b = this.___nodes___, 
      node /*: Ref(~lNode) */ = null, 
      on /*: Ref(~lEvent) */ = null, 
      ontype /*: Str */ = "";
  var i /*: {Int | (>= v 0)}*/ = 0;

  /*: b lNodes */ "#thaw";
  assume(b != null);
  /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> 
      sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];

//PV: slow-down
//    // The change event does not propogate, so we must put the handler on the
//    // instance.
//    if (type_ === 'change') {
//      ontype = 'on' + type_;
//      assume(ontype === 'onchange');
//      if (node[ontype] !== dom_event) {
//        node[ontype] = dom_event;
//      }
//    }
//
//    // Register an event. Put the function in a handler array, making one if it
//    // doesn't yet exist for this type_ on this node.
//
//    on = node['___ on ___'];
//    if (!on) {
//      var empty_ = /*: lEmpty Dict */ {};
//      /*: empty_ (~lEvent, frzn) */ "#freeze";
//      on = empty_;
//      node['___ on ___'] = on;
//    }
    
    /*: on lEvent */ "#thaw";
    assume(on != null);
//TODO    
    if (owns(on, type_)) {
      assume(typeof on === 'object');
      assume(isArray(on[type_]));
      on[type_].push(func);
    }
    else {
      on[type_] = [func];
    }
    /*: on (~lEvent, thwd lEvent) */ "#freeze";
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};
