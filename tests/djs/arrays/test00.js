
var a = /*: lA Arr(Top) */ [0,"hi",true];

/*: {(= v 0)} */ (/*: [Top;lA,lArrayProto;] */ a[0]);

/*: {(= v "hi")} */ (/*: [Top;lA,lArrayProto;] */ a[1]);

/*: {(= v true)} */ (/*: [Top;lA,lArrayProto;] */ a[2]);

/*: {(= v undefined)} */ (/*: [Top;lA,lArrayProto] */ a[3]);

/*: {(= v 3)} */ (/*: [Top;lA,lArrayProto;] */ a.length);

/*: {(= v 3)} */ (/*: [Top;lA,lArrayProto;] */ a["length"]);

var s = "length";

/*: {(= v 3)} */ (/*: [Top;lA,lArrayProto] */ a[s]);

var i = 1;

/*: {(= v "hi")} */ (/*: [Top;lA,lArrayProto;] */ a[i]);
