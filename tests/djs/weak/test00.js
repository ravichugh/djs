/*: (~lRow |-> Arr(Str) > lArrPro) */ "#weak";

var row1 = /*: lRow1 Arr(Str) */ ["00","01"];
var row2 = /*: lRow2 Arr(Str) */ ["10","11"];

assert (/*: Ref(lRow1) */ row1);
assert (/*: Ref(lRow2) */ row2);

/*: row1 (~lRow,frzn) */ "#freeze";
/*: row2 (~lRow,frzn) */ "#freeze";

assert (/*: Ref(~lRow) */ row1);
assert (/*: Ref(~lRow) */ row2);

var mat = /*: Arr(Ref(~lRow)) */ [row1, row2];

row1 = mat[0];
/*: row1 lThwd1 */ "#thaw";

var s = row1[0];

assert (/*: {(or (= v undefined) (Str v))} */ s);

s = (s == undefined ? "bleh" : s);

assert (/*: Str */ s);

// /*: {(= v true)} */ Array.isArray(row1);
