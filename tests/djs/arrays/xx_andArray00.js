var bs = /*: l */ [true, true, false];
var b = true;
var i;

/*: [&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> (_:Arr(Bool), lArrayProto)]
 -> [&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> (_:Arr(Bool), lArrayProto)] */
for (i = 0; i < bs.length; i++) {
  b = b && bs[i];
};

/*: Bool */ b;
