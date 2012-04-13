var x = {"f": 1};
assert (x.f == 1 && x.g == undefined);
x.g = 2; delete x.f;
assert (x.g == 2 && x.f == undefined);
var k = "h"; x[k] = 3; assert (x[k] == 3);
