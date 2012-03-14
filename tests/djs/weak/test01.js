/*: [~lRow |-> (frzn, Arr(Str), lArrayProto)] */ "#weak";

var row1 = /*: lRow1 <Str,Str> */ ["00","01"];
var row2 = /*: lRow2 <Str,Str> */ ["10","11"];

// /*: Ref(lRow1) */ row1;
// /*: Ref(lRow2) */ row2;
// 
// row1 = /*: ~lRow */ "#freeze";
// row2 = /*: ~lRow */ "#freeze";
// 
// /*: Ref(~lRow) */ row1;
// /*: Ref(~lRow) */ row2;
// 
// var mat = /*: Arr(Ref(~lRow)) */ [row1, row2];
// 
// row1 = mat[0];
// row1 = /*: lThwd1 */ "#thaw";
// 
// var s = row1[0];
// 
// /*: {(or (= v undefined) (v:Str))} */ s;
// 
// s = (s == undefined ? "bleh" : s);
// 
// /*: Str */ s;
// 
// // /*: {(= v true)} */ Array.isArray(row1);
