
var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v true)} */
(/*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(0));

/*: {(= v true)} */
(/*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(2));

/*: {(= v false)} */
(/*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(3));

