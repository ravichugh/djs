var bs = /*: l */ [true, true, false];
var b = true;
var i;

/*: (&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> _:<Bool,Bool,Bool> > lArrPro)
 -> (&bs |-> _:Ref(l), &b |-> _:Bool, &i |-> _:{Int|(>= v 0)},
     l |-> _:<Bool,Bool,Bool> > lArrPro) */
for (i = 0; i < bs.length; i++) {
  b = b && bs[i];
};

assert (typeof b == "boolean");
