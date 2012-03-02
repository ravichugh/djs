
var a = /*: lA */ [0,"hi",true];

/*: {(= v 0)} */ (/*: [Top;lA;] */ a[0]);

/*: {(= v "hi")} */ (/*: [Top;lA;] */ a[1]);

/*: {(= v True)} */ (/*: [Top;lA;] */ a[2]);

/*: {(= v undefined)} */ (/*: [Top;lA;] */ a[3]);

/*: {(= v 3)} */ (/*: [Top;lA;] */ a["length"]);

/*: {(= v 3)} */ (/*: [Top;lA;] */ a.length);

var s = "length";

/*: {(= v 3)} */ (/*: [Top;lA;] */ a[s]);

var i = 1;

/*: {(= v "hi")} */ (/*: [Top;lA;] */ a[i]);
