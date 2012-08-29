
var x = /*: lx */ {f:0, g:"hi"};

assert (/*: {(= v true)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("f")));

assert (/*: {(= v true)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("g")));

assert (/*: {(= v false)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("h")));

