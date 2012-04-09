var x = {};
var y = {"f": undefined};
assert (x.f == undefined && "f" in x == false);
assert (y.f == undefined && "f" in y == true);
