
var a = /*: lA Arr(Int) */ [0,1,2];

assert (/*: [Int;lA,lArrayProto;] */ a.length == 3);

(/*: [Int;lA,lArrayProto;] */ (a.push))(3);

assert (/*: [Int;lA,lArrayProto;] */ a.length == 4);

assert (/*: Int */ (/*: [Int;lA,lArrayProto;] */ a[3]));

(/*: [Int;lA,lArrayProto;] */ (a.pop))();

assert (/*: [Int;lA,lArrayProto;] */ a[3] == undefined);

