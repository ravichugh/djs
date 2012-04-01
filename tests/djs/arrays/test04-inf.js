
var arr = [0,1,2];

/*: {(= v true)} */ (0 in arr);

/*: {(= v true)} */ (2 in arr);

/*: {(= v false)} */ (3 in arr);

// note: can't prove anything about negative indices
(-1 in arr);

/*: {(= v true)} */ ("length" in arr);

/*: {(= v true)} */ ("push" in arr);

/*: {(= v false)} */ ("missing" in arr);
