
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var walkTheDOM = /*: ( node: Ref(~lNode), func:(Ref(~lNode)) -> Top, skip: Bool)
                   -> Top */ "#extern";

var purge_event_handlers = function(node) /*: (node: Ref(~lNode)) -> Top */
{

  // We attach all event handlers to an '___ on ___' property. The property name
  // contains spaces to insure that there is no collision with HTML attribues.
  // Keeping the handlers in a single property makes it easy to remove them
  // all at once. Removal is required to avoid memory leakage on IE6 and IE7.

  //PV: had to rename the argument's name
  walkTheDOM(node, function (node1) /*: (Ref(~lNode)) -> Top */
      {
        if (node1.tagName) {
          node1['___ on ___'] = node1.change = null;
        }
      },
      //PV: added third argument to match definition
      true
      );
};


