
var a = /*: lA Arr(Int) */ [0,1,2];

/*: [Int;lA,lArrayProto] */ a[3] = 3;
/*: [Int;lA,lArrayProto] */ a[4] = 4;
/*: [Int;lA,lArrayProto] */ a[5] = 5;

/*: {(= v 6)} */
(/*: [Int;lA,lArrayProto] */ a.length);

/*: [Int;lA,lArrayProto] */ a.length = 2;

/*: {(= v 2)} */
(/*: [Int;lA,lArrayProto] */ a.length);
