var row1 = ["00","01"];
var row2 = ["10","11"];

var mat = [row1, row2];

assert (mat[0][0] == "00");
assert (mat[0][1] == "01");
assert (mat[1][0] == "10");
assert (mat[1][1] == "11");

assert (mat[1][2] == undefined);
