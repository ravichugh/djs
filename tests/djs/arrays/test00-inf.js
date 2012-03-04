
var a = [0,"hi",true];

/*: {(= v 0)} */ (a[0]);

/*: {(= v "hi")} */ (a[1]);

/*: {(= v true)} */ (a[2]);

/*: {(= v undefined)} */ (a[3]);

/*: {(= v 3)} */ (a.length);

/*: {(= v 3)} */ (a["length"]);

var s = "length";

/*: {(= v 3)} */ (a[s]);

var i = 1;

/*: {(= v "hi")} */ (a[i]);
