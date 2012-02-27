var k = "g";
var x = {"f": k};
/*: {(= v True)} */ ("f" in x);

var xf = x.f;
/*: {(= v "g")} */ xf;

x[k] = 3;
/*: {(= v 3)} */ (x[k]);

delete x.f;
/*: {(= v False)} */ ("f" in x);

var y = x;
y.f = "hi";

xf = x.f;
/*: {(= v "hi")} */ xf;
