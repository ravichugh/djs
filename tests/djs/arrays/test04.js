
var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v true)} */
(0 in /*: [Int;lA,lArrayProto] */ a);

/*: {(= v true)} */
(2 in /*: [Int;lA,lArrayProto] */ a);

/*: {(= v false)} */
(3 in /*: [Int;lA,lArrayProto] */ a);

// note: can't prove anything about negative indices
(-1 in /*: [Int;lA,lArrayProto] */ a);

/*: {(= v true)} */
("length" in /*: [Int;lA,lArrayProto] */ a);

// TODO need to have syntactic rule to allow using prototype
// /*: {(= v true)} */
// ("push" in /*: [Int;lA,lArrayProto] */ a);

// TODO need to have unrolling bottom out at lROOT to prove this
// /*: {(= v false)} */
// ("missing" in /*: [Int;lA,lArrayProto] */ a);
