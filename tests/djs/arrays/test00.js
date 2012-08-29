
var a = /*: lA Arr(Top) */ [0,"hi",true];

assert (/*: [Top;lA,lArrayProto;] */ a[0] == 0);

assert (/*: [Top;lA,lArrayProto;] */ a[1] == "hi");

assert (/*: [Top;lA,lArrayProto;] */ a[2] == true);

assert (/*: [Top;lA,lArrayProto] */ a[3] == undefined);

assert (/*: [Top;lA,lArrayProto;] */ a.length == 3);

assert (/*: [Top;lA,lArrayProto;] */ a["length"] == 3);

var s = "length";

assert (/*: [Top;lA,lArrayProto] */ a[s] == 3);

var i = 1;

assert (/*: [Top;lA,lArrayProto;] */ a[i] == "hi");
