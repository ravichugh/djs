
////// need special typing rule for getElem on arrays and strings

var a = /*: lA Arr(Int) */ [0,1,2];

/*: {(= v 3)} */ (a.length);

a["push"](3);

/*: {(= v 4)} */ (a.length);

/*: Int */ (a[3]);

a["pop"]();

/*: {(= v undefined)} */ (a[3]);

