
var a = /*: lA */ [0,1,2];

/*: {(= v 3)} */ (/*: [Top;lA;] */ a.length);

/*: [Top;lA;] */ a.length = 2;

/*: {(= v 2)} */ (/*: [Top;lA;] */ a.length);

/*: {(= v undefined)} */ (/*: [Top;lA;] */ a[2]);

