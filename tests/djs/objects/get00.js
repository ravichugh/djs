var x = {f:1};

assert (x.f == 1);
assert (x.g == undefined);

// 8/29/12: no longer allowing natives to be modified
// Object.prototype.g = "yipee";
// assert (x.g == "yipee");
