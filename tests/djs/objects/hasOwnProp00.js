
var x = /*: lx */ {f:0, g:"hi"};

/*: {(= v True)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("f"));

/*: {(= v True)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("g"));

/*: {(= v False)} */
(/*: [;lx,lObjectProto;] */ (x.hasOwnProperty)("h"));

