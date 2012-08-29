
var a = /*: lA Arr(Int) */ [0,1,2];

assert (a.length == 3);

a.push(3);

assert (a.length == 4);

assert (/*: Int */ (a[3]));

a.pop();

assert (a[3] == undefined);

