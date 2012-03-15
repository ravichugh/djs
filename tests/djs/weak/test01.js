/*: [~lRow |-> (frzn, <Str,Str>, lArrayProto)] */ "#weak";

var row1 = /*: lRow1 */ ["00","01"];
var row2 = /*: lRow2 */ ["10","11"];

row1 = /*: ~lRow */ "#freeze";
row2 = /*: ~lRow */ "#freeze";

var mat = /*: Arr(Ref(~lRow)) */ [row1, row2];
 
row1 = mat[0];
row1 = /*: lThwd1 */ "#thaw";
 
var s0 = row1[0];
var s1 = row1[1];
var s2 = row1[2];

/*: Str */ s0;
/*: Str */ s1;
/*: {(= v undefined)} */ s2;

row1 = /*: ~lRow */ "#refreeze";

row2 = mat[0];
row2 = /*: lThwd1 */ "#thaw";
 
s0 = row2[0];
s1 = row2[1];
s2 = row2[2];

/*: Str */ s0;
/*: Str */ s1;
/*: {(= v undefined)} */ s2;

row2 = /*: ~lRow */ "#refreeze";
