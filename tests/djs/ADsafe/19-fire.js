var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

//XXX: owns  calls string_check on string so we can pass anything as 2nd
//argument
var owns = 
/*: (object: Ref, string: Top) / (object: d: Dict > lObjPro) 
      -> {Bool|(iff (= v true) (and (Str string) (has d string)))} / sameExact */ "#extern";


var reject_global = 
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */ "#extern";

var assumeObject = /*: [;L,Lp] () / () -> Ref(L) / (L: Dict > Lp) */ "#extern";
// -----------------------------------------------------------------------------------


var fire = function (event) 
/*: (this: Ref(~lBunch), event: Top) -> Ref(~lBunch) */ 
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
      j /*: { Int | (>= v 0)} */ = 0,
      n,
      node /*: Ref(~htmlElt) */ = null,
      on /*: Ref(~lEvent) */ = null,
      type;

  if (typeof event === 'string') {
    type = event;
    event = {type_: type};
  }
  else if (typeof event === 'object') {
    event = /*: [;l1,l2] */ assumeObject();
    type = event.type_;
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
      assert(type in on);
      //TODO: we avoided using intersection type by using Top as argument,
      //but here there's nothing we can do, as there is no guarantee that 
      //the field we retrieve from "on" is the desired one.
      assume(type === "array");
      var array = on[type];
      /*: on (~lEvent, thwd lEvent) */ "#freeze";
      
      assert(/*: Ref(~lFuncs) */ (array));
      /*: array lArray */ "#thaw";
      assume(array != null);
      //XXX: SUPER UGLY: figure out how to TC without this monstrosity 
      /*: ( &array: Ref(lArray), 
            lArray: {Arr( (Top,Top) / (&array: Ref(lArray),
                          lArray: {Arr((Top,Top)-> Top)|(packed v)} > lArrPro) -> Top / sameExact 
                        )|(packed v)} > lArrPro)
          -> sameExact */
      for (j = 0; j < array.length; j += 1) {

        // Invoke a handler. Pass the event object.        
    
        //PV: original code begin
        //array[j].call(this, event);
        //PV: original code end
        array[j](this, event);
      }
    /*: array (~lFuncs, thwd lArray) */ "#freeze";
    }
    else {
      /*: on (~lEvent, thwd lEvent) */ "#freeze";
    }
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return this;
};
