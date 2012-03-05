var bs = /*: l */ [true, true, false];
var b = true;
var i;

/*: [&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> (_:<Bool,Bool,Bool>, lArrayProto)]
 -> [&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> (_:<Bool,Bool,Bool>, lArrayProto)] */
for (i = 0; i < bs.length; i++) {
  /*: {(= v 3)} */ (bs.length);
  /*: {(and (>= v 0) (< v 3))} */ (i);
  /*: {(not (= v undefined))} */ (bs[i]);
  /*: Bool */ (bs[0]);
  /*: Bool */ (bs[1]);
  /*: Bool */ (bs[2]);
  /*: {(or (= v 0) (= v 1) (= v 2))} */ (i);
  /*: Bool */ (bs[i]);
};
