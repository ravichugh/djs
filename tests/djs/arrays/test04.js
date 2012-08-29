
var a = /*: lA Arr(Int) */ [0,1,2];

assert (true == 0 in /*: [Int;lA,lArrayProto] */ a);

assert (true == 2 in /*: [Int;lA,lArrayProto] */ a);

assert (false == 3 in /*: [Int;lA,lArrayProto] */ a);

// note: can't prove anything about negative indices
(-1 in /*: [Int;lA,lArrayProto] */ a);

assert (true == "length" in /*: [Int;lA,lArrayProto] */ a);

assert (true == "push" in /*: [Int;lA,lArrayProto] */ a);

assert (false == "missing" in /*: [Int;lA,lArrayProto] */ a);
