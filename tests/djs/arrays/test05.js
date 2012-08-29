
var a = /*: lA Arr(Int) */ [0,1,2];

assert (true == /*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(0));

assert (true == /*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(2));

assert (false == /*: [Int;lA,lArrayProto] */ (a.hasOwnProperty)(3));

