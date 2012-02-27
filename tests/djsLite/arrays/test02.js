
var a = /*: lA Arr(Int) */ [0,1,2];

(/*: [Int;lA;] */ a[/*: [Int;lA;] */ a.length] = (/*: [Int;lA;] */ a.length));
(/*: [Int;lA;] */ a[/*: [Int;lA;] */ a.length] = (/*: [Int;lA;] */ a.length));
(/*: [Int;lA;] */ a[/*: [Int;lA;] */ a.length] = (/*: [Int;lA;] */ a.length));

/*: {(= v 6)} */ (/*: [Int;lA;] */ a.length);

