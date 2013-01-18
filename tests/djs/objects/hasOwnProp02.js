var foo = function (node)
/*: (node: Ref)
  / (node: {Dict|(and (not (has v "hasOwnProperty"))
                      (= (heapsel cur node.pro "hasOwnProperty")
                         (sel theObjPro "hasOwnProperty")))} > node.pro)
 -> Bool / (node: sameExact) */
{ 
  return node.hasOwnProperty("h");
};
