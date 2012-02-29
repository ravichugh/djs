
var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v 3)} */
(/*: [Int;lA,lArrayProto;] */ a.length);

(/*: [Int;lA,lArrayProto;] */ (a.push))(3);

/*: {(= v 4)} */
(/*: [Int;lA,lArrayProto;] */ a.length);

/*: Int */
(/*: [Int;lA,lArrayProto;] */ a[3]);

(/*: [Int;lA,lArrayProto;] */ (a.pop))(3);

/*: {(= v undefined)} */
(/*: [Int;lA,lArrayProto;] */ a[3]);

