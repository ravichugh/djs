
var x = /*: lx */ {f:0, g:"hi"};
assert(/*: Ref(lx) */ (x));

assert (/*: {(= v true)} */
(/*: [;lx,lObjPro;] */ (x.hasOwnProperty)("f")));

assert (/*: {(= v true)} */
(/*: [;lx,lObjPro;] */ (x.hasOwnProperty)("g")));

assert (/*: {(= v false)} */
(/*: [;lx,lObjPro;] */ (x.hasOwnProperty)("h")));

assert (/*: {(= v false)} */
((x.hasOwnProperty)("h")));

//TODO: how to avoid defining the type for hasOwnProperty
//var foo = function (node) 
///*: (node: Ref) / 
//        (
//          node:
//              {
//                "hasownproperty": {(v:: (this:ref, kk: str) / (this: dd : dict > lobjpro) -> 
//                    {bool | (iff (= v true) (has dd kk))} / same )}  
//              } > lobjpro
//        ) 
//    -> bool / same */
//{
//  return node.hasownproperty("h");
//};

var bar = function (node)
/*: (node: Ref) / (node: {"h": Bool }  > theObjPro) -> Bool / (node: sameType) */
{ 
  assert(/*: Bool */ ((node.hasOwnProperty) ("h")));
  return true; 
};




