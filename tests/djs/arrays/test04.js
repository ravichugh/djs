
var a = /*: lA Arr(Int) */ [0,1,2];

assert (true == 0 in /*: [Int;lA,lArrPro] */ a);

assert (true == 2 in /*: [Int;lA,lArrPro] */ a);

assert (false == 3 in /*: [Int;lA,lArrPro] */ a);

// note: can't prove anything about negative indices
(-1 in /*: [Int;lA,lArrPro] */ a);

assert (true == "length" in /*: [Int;lA,lArrPro] */ a);

assert (true == "push" in /*: [Int;lA,lArrPro] */ a);

assert (false == "missing" in /*: [Int;lA,lArrPro] */ a);
