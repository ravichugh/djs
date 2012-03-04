
var a = [0,1,2];

/*: {(= v true)} */ (0 in a);

/*: {(= v true)} */ (2 in a);

/*: {(= v false)} */ (3 in a);

// note: can't prove anything about negative indices
(-1 in a);

/*: {(= v true)} */ ("length" in a);

// TODO need to have syntactic rule to allow using prototype
// /*: {(= v true)} */
// ("push" in /*: [Int;lA,lArrayProto] */ a);

// TODO need to have unrolling bottom out at lROOT to prove this
// /*: {(= v false)} */
// ("missing" in /*: [Int;lA,lArrayProto] */ a);
