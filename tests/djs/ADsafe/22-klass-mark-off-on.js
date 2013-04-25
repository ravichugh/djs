var error = /*: {( and 
              (v:: (message: Str)  -> { FLS })
              (v:: ()  -> { FLS })              
              )} */ "#extern";
var dom_event = /*: (this: Ref(~lEvent), Ref(~lEvent))-> Top */ "#extern";

var owns = 
/*: (object: Ref, string: Str) / (object: d: Dict > object.pro) -> 
      {Bool|(and  (iff (= v false) (not (has d string)))  (iff (= v true) (has d string)))} / sameExact */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyEvent {
  altKey          : Bool,
  bubble          : (this: Ref(~lEvent))-> Top,
  cancelBubble    : Bool,
  ctrlKey         : Bool,
  key             : Str, 
  preventDefault  : (this: Ref(~lEvent)) -> Top,
  shiftKey        : Bool,
  srcElement      : Ref(~htmlElt),
  stopPropagation : (this: Ref(~lEvent))-> Top,
  target          : Ref(~htmlElt),    (* could also be Ref(~lEventTarget) *)
  that            : Ref(~lBunch),
  type_           : Str,
  _               : Bot
} */ "#define";


var String =  /*: (Top) -> Str */ "#extern";

var allow_focus /*: Bool */ = "#extern";
var star    /*: Bool */         = "#extern";
var the_range /*: Ref(~lRange) */  = "#extern";

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
  var b = this.___nodes___, node /*: Ref(~htmlElt) */ = null;
  var i /*: {Int | (>= v 0)}*/ = 0;
  if (isArray(value)) {
    /*: b htmlElts */ "#thaw";
    if (value.length !== b.length) {
      error('ADsafe: Array length: ' /*+ int_to_string(b.length) + '-' +
         int_to_string(value.length)*/);
    }
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagName) {
        node['_adsafe mark_'] = String(value[i]);
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  } 
  else {
    /*: b htmlElts */ "#thaw";
    b.l;
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagName) {
        node['_adsafe mark_'] = String(value);
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  return this;
};

var off = function (type_) /*: (this: Ref(~lBunch), type_:Top) -> Ref(~lBunch) */ {
  reject_global(this);
  var b = this.___nodes___, 
      node /*: Ref(~htmlElt) */ = null;
  var i /*: {Int | (>= v 0)}*/ = 0;
  /*: b htmlElts */ "#thaw";
  assume(b != null);
  /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    /*: node htmlElt */ "#thaw";
    assume(node != null);
    if (typeof type_ === 'string') {
      var e = node['___ on ___'];
      /*: e lEvent */ "#thaw";
      assume(e != null);
      if (typeof e) {
        //PV: will have to use this here cause we might be overwriting 
        //an existing field with an incompatible type.
        assume(type_ === "nonexisting_string");
        e[type_] = null;
      }
      /*: e (~lEvent, thwd lEvent) */ "#freeze";
    } else {
      //TODO
      //node['___ on ___'] = null;
    }
    /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
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
      node /*: Ref(~htmlElt) */ = null, 
      on /*: Ref(~lEvent) */ = null, 
      ontype /*: Str */ = "";
  var i /*: {Int | (>= v 0)}*/ = 0;

  /*: b htmlElts */ "#thaw";
  assume(b != null);
  /*: ( &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> 
      sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];

//PV: Slow Down !!! ~ 45 sec
    // The change event does not propogate, so we must put the handler on the
    // instance.
    if (type_ === 'change') {
      ontype = 'on' + type_;
      assume(ontype === 'onchange');
      /*: node htmlElt */ "#thaw";
      assume(node != null);
      if (node[ontype] !== dom_event) {
        node[ontype] = dom_event;
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }

    // Register an event. Put the function in a handler array, making one if it
    // doesn't yet exist for this type_ on this node.

    on = node['___ on ___'];
    if (!on) {
      var empty_ = /*: lEmpty Dict */ { type_: "" };  //PV: meh...
      /*: empty_ (~lEvent, frzn) */ "#freeze";
      on = empty_;
      node['___ on ___'] = on;
    }
    
    /*: on lEvent */ "#thaw";
    assume(on != null);
    //TODO    
    if (owns(on, type_)) {
      assert(type_ in on);
      //assume(typeof on === 'object');
      //assume(isArray(on[type_]));
      //on[type_].push(func);
    }
    else {
      //TODO
      assume(type_ === "nonexisting_field");
      on[type_] = [func];
    }
    /*: on (~lEvent, thwd lEvent) */ "#freeze";
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return this;
};
