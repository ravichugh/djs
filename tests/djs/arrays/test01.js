
var a = /*: lA Arr(Int) */ [0,1,2];

assert (/*: [Int;lA,lArrPro;] */ a.length == 3);

(/*: [Int;lA,lArrPro;] */ (a.push))(3);

assert (/*: [Int;lA,lArrPro;] */ a.length == 4);

assert (/*: Int */ (/*: [Int;lA,lArrPro;] */ a[3]));

(/*: [Int;lA,lArrPro;] */ (a.pop))();

assert (/*: [Int;lA,lArrPro;] */ a[3] == undefined);

