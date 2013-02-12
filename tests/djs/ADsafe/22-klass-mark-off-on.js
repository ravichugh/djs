/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyEvent {
  type_           : Str,
  target          : Ref(~lNode),    (* could also be Ref(~lEventTarget) *)
  cancelBubble    : Bool,
  stopPropagation : () -> Top,
  bubble          : () -> Top,
  srcElement      : Ref(~lNode),
  altKey          : Bool,
  ctrlKey         : Bool,
  shiftKey        : Bool
} > lObjPr */ "#define";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var String =  /*: (Top) -> Str */ "#extern";

//TODO
var klass = function (value) 
/*: (this: Ref(~lBunch), value: Str) -> Top */
{
//  return this['class'](value);
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
//TODO      
//      error('ADsafe: Array length: ' + b.length + '-' +
//          value.length);
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

var off = function (type_) 
/*: (this: Ref(~lBunch), type_:Top) -> Ref(~lBunch) */
{
  reject_global(this);
  var b = this.___nodes___, node /*: Ref(~lNode) */ = null;
  var i /*: {Int | (>= v 0)}*/ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    if (typeof type_ === 'string') {
      if (typeof node['___ on ___']) {
//TODO: What are the values that type_ can have?
//        node['___ on ___'][type_] = null;
      }
    } else {
      node['___ on ___'] = null;
    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};

var on = function (type_, func) 
/*: (this: Ref(~lBunch), type_:Top, func: (Top) -> Top) -> Ref(~lBunch) */
{
  reject_global(this);
  if (typeof type_ !== 'string' || typeof func !== 'function') {
    error("default");
  }

  var b = this.___nodes___, 
      node /*: Ref(~lNode) */ = null, 
      on, //PV
      ontype /*: Str */ = "";
  var i /*: {Int | (>= v 0)}*/ = 0;

  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> 
      sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];

    // The change event does not propogate, so we must put the handler on the
    // instance.
//TODO
    if (type_ === 'change') {
//      ontype = 'on' + type_;
//      if (node[ontype] !== dom_event) {
//        node[ontype] = dom_event;
//      }
    }

    // Register an event. Put the function in a handler array, making one if it
    // doesn't yet exist for this type_ on this node.

//    on = node['___ on ___'];
//    if (!on) {
//      /*: on lEvent */ "#thaw";
//      on = {};
//      node['___ on ___'] = on;
//    }
//    if (owns(on, type_)) {
//      on[type_].push(func);
//    } else {
//      on[type_] = [func];
//      /*: on (~lEvent, thwd lEvent) */ "#freeze";
//    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};
