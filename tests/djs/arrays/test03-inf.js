
var a = /*: lA Arr(Int) */ [0,1,2];

a[3] = 3;
a[4] = 4;
a[5] = 5;

/*: {(= v 6)} */ (a.length);

a.length = 2;

/*: {(= v 2)} */ (a.length);
