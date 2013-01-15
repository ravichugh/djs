var b = /*: Bool */ "#extern";
var n = 1.0;
if (b) { n = 2.0; }
var s = n.toString();
assert (typeof s === "string");
