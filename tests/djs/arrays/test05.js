
var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v True)} */
(/*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(0));

/*: {(= v True)} */
(/*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(2));

/*: {(= v False)} */
(/*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(3));

