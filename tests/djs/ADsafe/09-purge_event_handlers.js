/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
 
var walkTheDOM = 
/* (this:Top, Ref(~htmlElt)) / (~htmlElts: frzn, ~lChecked: frzn, ~lClassNames:
   frzn, ~lADsafeMarks: frzn, ~lNames: frzn, ~lPackedValues: frzn, ~lValues:
   frzn, ~lOffsetHeights: frzn, ~lOffsetWidths: frzn, ~lKeys: frzn, ~lStyles:
   frzn, ~lEvent: frzn, ~lEventTarget: frzn, ~lSelector: frzn, ~lRange: frzn,
   ~lQuery: frzn, ~lBunches: frzn, ~lBunch: frzn, ~lStyle: frzn, ~lSelection:
   frzn, ~htmlElt: frzn, ~lDocument: frzn, ~lDom: frzn, ~lF: frzn, ~lId: frzn,
   ~lLib: frzn) -> Top / (~htmlElts: frzn, ~lChecked: frzn, ~lClassNames: frzn,
   ~lADsafeMarks: frzn, ~lNames: frzn, ~lPackedValues: frzn, ~lValues: frzn,
   ~lOffsetHeights: frzn, ~lOffsetWidths: frzn, ~lKeys: frzn, ~lStyles: frzn,
   ~lEvent: frzn, ~lEventTarget: frzn, ~lSelector: frzn, ~lRange: frzn, ~lQuery:
   frzn, ~lBunches: frzn, ~lBunch: frzn, ~lStyle: frzn, ~lSelection: frzn,
   ~htmlElt: frzn, ~lDocument: frzn, ~lDom: frzn, ~lF: frzn, ~lId: frzn, ~lLib:
   frzn) */

/*: ( node: Ref(~htmlElt), func:(Ref(~htmlElt)) -> Top, skip: Bool) -> Top */ "#extern";

var purge_event_handlers = function(node) /*: (node: Ref(~htmlElt)) -> Top */
{

  // We attach all event handlers to an '___ on ___' property. The property name
  // contains spaces to insure that there is no collision with HTML attribues.
  // Keeping the handlers in a single property makes it easy to remove them
  // all at once. Removal is required to avoid memory leakage on IE6 and IE7.
  
  //PV: had to rename the argument's name
  walkTheDOM(node, function (node_) /*: (Ref(~htmlElt)) -> Top */
      {
        if (node_.tagName) {
          node_['___ on ___'] = node_.change = null;
        }
      },
      //PV: added third argument to match definition
       true
      );
};


