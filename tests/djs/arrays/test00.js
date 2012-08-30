
var a = /*: lA Arr(Top) */ [0,"hi",true];

assert (/*: [Top;lA,lArrPro;] */ a[0] == 0);

assert (/*: [Top;lA,lArrPro;] */ a[1] == "hi");

assert (/*: [Top;lA,lArrPro;] */ a[2] == true);

assert (/*: [Top;lA,lArrPro] */ a[3] == undefined);

assert (/*: [Top;lA,lArrPro;] */ a.length == 3);

assert (/*: [Top;lA,lArrPro;] */ a["length"] == 3);

var s = "length";

assert (/*: [Top;lA,lArrPro] */ a[s] == 3);

var i = 1;

assert (/*: [Top;lA,lArrPro;] */ a[i] == "hi");
