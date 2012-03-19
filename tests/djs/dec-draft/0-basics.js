var k = "g";
var x = {"f": k};
assert ("f" in x);

var xf = x.f;
assert (xf == "g");

x[k] = 3;
assert (x[k] == 3);

delete x.f;
assert (!("f" in x));

var y = x;
y.f = "hi";

xf = x.f;
assert (xf == "hi");
