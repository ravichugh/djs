/*: (~lRow |-> Arr(Str) > lArrPro) */ "#weak";

var row1 = /*: lRow1 Arr(Str) */ ["00","01"];
var row2 = /*: lRow2 Arr(Str) */ ["10","11"];

assert (/*: Ref(lRow1) */ row1);
assert (/*: Ref(lRow2) */ row2);

/*: row1 (~lRow,frzn) */ "#freeze";

// row2 not frozen
var mat = /*: Arr(Ref(~lRow)) */ [row1, row2];
