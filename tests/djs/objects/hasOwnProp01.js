var foo = function (node)
/*: (node: Ref) / (node: {Dict|(not (has v "hasOwnProperty"))} > lObjPro)
 -> Bool / (node: sameExact) */
{ 
  return node.hasOwnProperty("h");
};
