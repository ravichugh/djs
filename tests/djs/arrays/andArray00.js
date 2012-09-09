var bs = /*: l */ [true, true, false];
var b = true;
var i;

/*: (&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> _:<Bool,Bool,Bool> > lArrPro)
 -> (&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> _:<Bool,Bool,Bool> > lArrPro)) */
for (i = 0; i < bs.length; i++) {
  assert (/*: {(= v 3)} */ (bs.length));
  assert (/*: {(and (>= v 0) (< v 3))} */ (i));
  assert (/*: {(not (= v undefined))} */ (bs[i]));
  assert (/*: Bool */ (bs[0]));
  assert (/*: Bool */ (bs[1]));
  assert (/*: Bool */ (bs[2]));
  assert (/*: {(or (= v 0) (= v 1) (= v 2))} */ (i));
  assert (/*: Bool */ (bs[i]));
};
