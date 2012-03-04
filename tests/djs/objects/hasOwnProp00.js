
var x = /*: lx */ {f:0, g:"hi"};

/*: {(= v true)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("f"));

/*: {(= v true)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("g"));

/*: {(= v false)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("h"));

