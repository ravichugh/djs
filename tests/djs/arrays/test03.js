
var a = /*: lA Arr(Int) */ [0,1,2];

/*: [Int;lA,lArrPro] */ a[3] = 3;
/*: [Int;lA,lArrPro] */ a[4] = 4;
/*: [Int;lA,lArrPro] */ a[5] = 5;

assert (/*: [Int;lA,lArrPro] */ a.length == 6);

/*: [Int;lA,lArrPro] */ a.length = 2;

assert (/*: [Int;lA,lArrPro] */ a.length == 2);
