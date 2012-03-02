
var a = /*: lA Arr(Int) */ [0,1,2];

a[a.length] = a.length;
a[a.length] = a.length;
a[a.length] = a.length;

/*: {(= v 6)} */ (a.length);

