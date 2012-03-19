/*: [~lRow |-> (Arr(Str), lArrayProto)] */ "#weak";

var row1 = /*: lRow1 Arr(Str) */ ["00","01"];
var row2 = /*: lRow2 Arr(Str) */ ["10","11"];

/*: Ref(lRow1) */ row1;
/*: Ref(lRow2) */ row2;

/*: row1 (~lRow,frzn) */ "#freeze";

// row2 not frozen
var mat = /*: Arr(Ref(~lRow)) */ [row1, row2];
