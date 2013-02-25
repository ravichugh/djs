var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyEvent {
  type_           : Str,
  target          : Ref(~lNode),
  cancelBubble    : Bool,
  stopPropagation : (this: Ref(~lEvent))-> Top,
  bubble          : (this: Ref(~lEvent))-> Top,
  preventDefault  : (this: Ref(~lEvent)) -> Top,
  srcElement      : Ref(~lNode),
  key             : Str, 
  altKey          : Bool,
  ctrlKey         : Bool,
  shiftKey        : Bool,
  that            : Ref(~lBunch),
  _               : Bot
} */ "#define";


//var owns = 
///*: (object: Ref, string: Str) / (object: d: tyEvent > lObjPro) -> 
//    {Bool|(implies (= v true) (has d {string}))} / sameType */ "#extern";

var owns = 
/*: (object: Ref, string: Str) / (object: Dict > lObjPro) -> Bool / sameType */ "#extern";

var reject_global = /*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";


// -----------------------------------------------------------------------------------


var fire = function (event) 
/*: {(and
    (v :: (this: Ref(~lBunch), event: Str) -> Ref(~lBunch))
    (v :: (this: Ref(~lBunch), event: Ref(~lEvent)) -> Ref(~lBunch))
    )} */

{
  // Fire an event on an object. The event can be either
  // a string containing the name of the event, or an
  // object containing a type property containing the
  // name of the event. Handlers registered by the 'on'
  // method that match the event name will be invoked.

  reject_global(this);
  var array,
      b,      
      i /*: { Int | (>= v 0)} */ = 0,
      j,
      n,
      node /*: Ref(~lNode) */ = null,
      on /*: Ref(~lEvent) */ = null,
      type /*: Str */ = "";

  if (typeof event === 'string') {
//    assert(/*: Str */ (event));
//    type = event;
//    event = {type_: type};
  }
  else if (typeof event === 'object') {
    assert(/*: Ref(~lEvent) */ (event));
//    /*: event lEvent */ "#thaw";
//    type = event.type_;
//    /*: event (~lEvent, thwd lEvent) */ "#freeze";
  } 
  else {
//    error();
  }

  b = this.___nodes___;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: (lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    on = node['___ on ___'];

    // If an array of handlers exist for this event, then
    // loop through it and execute the handlers in order.
  
//TODO      
//    /*: on lEvent */ "#thaw";
//    if (owns(on, type)) {
//      array = on[type];
//      for (j = 0; j < array.length; j += 1) {
//
//        // Invoke a handler. Pass the event object.
//
//        array[j].call(this, event);
//      }
//    }
//    /*: on (~lEvent, thwd lEvent) */ "#freeze";
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};
