
var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v True)} */ (0 in a);

/*: {(= v True)} */ (2 in a);

/*: {(= v False)} */ (3 in a);

// note: can't prove anything about negative indices
(-1 in a);

/*: {(= v True)} */ ("length" in a);

// TODO need to have syntactic rule to allow using prototype
// /*: {(= v True)} */
// ("push" in /*: [Int;lA,lArrayProto] */ a);

// TODO need to have unrolling bottom out at lROOT to prove this
// /*: {(= v False)} */
// ("missing" in /*: [Int;lA,lArrayProto] */ a);
