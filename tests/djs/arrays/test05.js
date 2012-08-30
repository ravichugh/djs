
var a = /*: lA Arr(Int) */ [0,1,2];

assert (true == /*: [Int;lA,lArrPro] */ (a.hasOwnProperty)(0));

assert (true == /*: [Int;lA,lArrPro] */ (a.hasOwnProperty)(2));

assert (false == /*: [Int;lA,lArrPro] */ (a.hasOwnProperty)(3));

