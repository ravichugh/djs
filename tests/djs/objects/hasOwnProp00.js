
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
