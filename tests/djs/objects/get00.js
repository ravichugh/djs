var x = {f:1};

assert (x.f == 1);
assert (x.g == undefined);

Object.prototype.g = "yipee";

assert (x.g == "yipee");
