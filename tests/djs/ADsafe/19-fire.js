var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var owns = 
/*: (object: Ref, string: Str) / (object: d: Dict > lObjPro) 
      -> {Bool|(iff (= v true) (has d string))} / sameExact */ "#extern";


var reject_global = 
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */ "#extern";


// -----------------------------------------------------------------------------------


var fire = function (event) 
//TODO: intersection type won't work
/* {(and
    (v :: (this: Ref(~lBunch), event: {Str|(= v "__farray__")}) -> Ref(~lBunch)) 
    (v :: (this: Ref(~lBunch), event: {(and (v::Ref(~lEvent)))}) -> Ref(~lBunch)) 
    )} */
  
/* (this: Ref(~lBunch), event: Str) -> Ref(~lBunch) */ 
/*: (this: Ref(~lBunch), event: {(and (= (tag v) "object") (v::Ref(~lEvent)))}) -> Ref(~lBunch) */

{
  // Fire an event on an object. The event can be either
  // a string containing the name of the event, or an
  // object containing a type property containing the
  // name of the event. Handlers registered by the 'on'
  // method that match the event name will be invoked.

  /*: this lBunch */ "#thaw";
  assume(this != null);
  reject_global(this);
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var 
      b,      
      i /*: { Int | (>= v 0)} */ = 0,
      j,
      n,
      node /*: Ref(~htmlElt) */ = null,
      on /*: Ref(~lEvent) */ = null,
      type /*: Str */ = "";

//  assert(/*: {(implies (Str v) (= v "__farray__"))} */ (event));

  if (typeof event === 'string') {
    type = event;
    event = {type_: type};
  }
  else if (typeof event === 'object') {
    assert(/*: Ref(~lEvent) */ (event));
    /*: event lEvent */ "#thaw";
    assume(event != null);
    type = event.type_;
    /*: event (~lEvent, thwd lEvent) */ "#freeze";
  }
  else {
    error();
  }

  b = this.___nodes___;
  /*: b htmlElts */ "#thaw";
  assume(b!=null);
  /*: (htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    on = node['___ on ___'];

    // If an array of handlers exist for this event, then
    // loop through it and execute the handlers in order.
  
    /*: on lEvent */ "#thaw";
    assume(on != null);
    if (/*: [;lEvent] */ owns(on, type)) {
      var array = on[type];
//TODO: no way this is gonna be an array...      
//      for (j = 0; j < array.length; j += 1) {
//
//        // Invoke a handler. Pass the event object.
//
//        array[j].call(this, event);
//      }
    }
    /*: on (~lEvent, thwd lEvent) */ "#freeze";
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return this;
};
