/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var owns = 
/*: [;L;](object: Ref(L), string: Str) / (L: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
    { (implies (= v true) (has d {string}))} / sameType */ "#extern";

var fire = function (event) 
/*: {(and
    (v :: (this: Ref(~lBunch), event: Str) -> Ref(~lBunch))
    (v :: (this: Ref(~lBunch), event: Ref(~lEvent)) -> Ref(~lBunch)))} */

{
  // Fire an event on an object. The event can be either
  // a string containing the name of the event, or an
  // object containing a type property containing the
  // name of the event. Handlers registered by the 'on'
  // method that match the event name will be invoked.

  //reject_global(this);
  var array,
      b,      
      i /*: { Int | (>= v 0)} */ = 0,
      j,
      n,
      node /*: Ref(~lNode) */ = null,
      on /*: Ref(~lEvent) */ = null,
      type /*: Str */ = "";

  if (typeof event === 'string') {
    type = event;
    event = {type_: type};
  }
  else if (typeof event === 'object') {
    type = event.type_;
  } 
  else {
    //error();
  }

  /*: this lBunch */ "#thaw";
  b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  /*: b lNodes */ "#thaw";
  b.l;
  /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    on = node['___ on ___'];

    // If an array of handlers exist for this event, then
    // loop through it and execute the handlers in order.
  
//TODO:     
//    if (owns(on, type)) {
//      array = on[type];
//      for (j = 0; j < array.length; j += 1) {
//
//        // Invoke a handler. Pass the event object.
//
//        array[j].call(this, event);
//      }
//    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};
