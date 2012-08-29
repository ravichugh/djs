
var a = [0,"hi",true];

assert (a[0] == 0);

assert (a[1] == "hi");

assert (a[2] == true);

assert (a[3] == undefined);

assert (a.length == 3);

assert (a["length"] == 3);

var s = "length";

assert (a[s] == 3);

var i = 1;

assert (a[i] == "hi");
