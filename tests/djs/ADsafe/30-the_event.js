
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";

var star             /*: Bool */         = "#extern";
var value            /*: Str */          = "#extern";
var int_to_string    /*: (Int) -> Str */ = "#extern";
var the_actual_event /*: Ref(~lEvent) */ = "#extern";
var that             /*: Ref(~lNode) */  = "#extern";
var key              /*: Str */          = "#extern";
var type             /*: Str */          = "#extern";
var target           /*: Ref(~lBunch) */ = "#extern";


//PV: wrapping it up in a function to force heap updates
var foo = function() /*: () -> Top */
{

  
  var the_event = {
    altKey: the_actual_event.altKey,
    ctrlKey: the_actual_event.ctrlKey,
//    //TODO: - try-catch                          
//    //      - self-reference
//    bubble: function () /*: () -> Top */
//    {
//
//      // Bubble up. Get the parent of that node. It becomes the new that.
//      // getParent throws when bubbling is not possible.
//
//      //    try {
//            var parent = that.getParent(),
////PV: is this safe?
////            b = parent.___nodes___[0];
//            that = parent;
//            the_event.that = that;
//      
//            // If that node has an event handler, fire it. Otherwise, bubble up.
//      
//            if (b['___ on ___'] &&
//                b['___ on ___'][type]) {
//                  that.fire(the_event);
//                } else {
//                  the_event.bubble();
//                }
//      //    } catch (e) {
//      //      error(e);
//      //    }
//    }
    key: key,
    preventDefault: function () 
    /*: () -> Top */
    {
      if (the_actual_event.preventDefault) {
        the_actual_event.preventDefault();
      }
      the_actual_event.returnValue = false;
    },
    shiftKey: the_actual_event.shiftKey,
    target: target,
    that: that,
    type: type,
    x: the_actual_event.clientX,
    y: the_actual_event.clientY
  };
};

