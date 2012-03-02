
var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v True)} */ (a.hasOwnProperty(0));

/*: {(= v True)} */ (a.hasOwnProperty(2));

/*: {(= v False)} */ (a.hasOwnProperty(3));

