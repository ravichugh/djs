
var a = /*: lA Arr(Int) */ [0];

/*: {(= v 1)} */ (/*: [Int;lA;] */ a.length);

/*: [Int;lA;] */ a[1] = 1;

/*: {(= v 2)} */ (/*: [Int;lA;] */ a.length);

/*: [Int;lA;] */ a[1] = 11111;

/*: {(= v 2)} */ (/*: [Int;lA;] */ a.length);

/*: [Int;lA;] */ a[2] = 2;

/*: {(= v 3)} */ (/*: [Int;lA;] */ a.length);

var i = 3;

/*: [Int;lA;] */ a[i] = 3;

/*: {(= v 4)} */ (/*: [Int;lA;] */ a.length);

i = 4;

/*: [Int;lA;] */ a[i] = 4;

/*: {(= v 5)} */ (/*: [Int;lA;] */ a.length);

