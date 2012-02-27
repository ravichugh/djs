
var a = /*: lA */ [0,1,2];

/*: {(= v 3)} */ (/*: [;lA;] */ a.length);

/*: [;lA;] */ a.length = 2;

/*: {(= v 2)} */ (/*: [;lA;] */ a.length);

/*: {(= v undefined)} */ (/*: [;lA;] */ a[2]);

