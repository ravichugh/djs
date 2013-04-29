/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var walkTheDOM = function walkTheDOM_rec(node, func, skip) 
  /*: ( node: Ref(~htmlElt), func:(Ref(~htmlElt)) -> Top, skip: Bool) -> Top */
{

  // Recursively traverse the DOM tree, starting with the node, in document
  // source order, calling the func on each node visisted.

  if (!skip) {
    func(node);
  }
  node = node.firstChild;
  /*: (&node: Ref(~htmlElt)) -> (&node: sameType) */
  while (node) {
    walkTheDOM_rec(node, func, true);   //PV added third argument to match definition
    node = node.nextSibling;
  }
};
