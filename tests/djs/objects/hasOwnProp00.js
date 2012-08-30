
var x = /*: lx */ {f:0, g:"hi"};

assert (/*: {(= v true)} */
(/*: [;lx,lObjPro;] */ (x.hasOwnProperty)("f")));

assert (/*: {(= v true)} */
(/*: [;lx,lObjPro;] */ (x.hasOwnProperty)("g")));

assert (/*: {(= v false)} */
(/*: [;lx,lObjPro;] */ (x.hasOwnProperty)("h")));

