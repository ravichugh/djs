var k = "g";
var x = {"f": k};
/*: {(= v true)} */ ("f" in x);

var xf = x.f;
/*: {(= v "g")} */ xf;

x[k] = 3;
/*: {(= v 3)} */ (x[k]);

// TODO
// delete x.f;
// /*: {(= v false)} */ ("f" in x);

var y = x;
y.f = "hi";

xf = x.f;
/*: {(= v "hi")} */ xf;
