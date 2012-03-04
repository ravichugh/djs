
var a = [0,1,2];

/*: {(= v true)} */ (a.hasOwnProperty(0));

/*: {(= v true)} */ (a.hasOwnProperty(2));

/*: {(= v false)} */ (a.hasOwnProperty(3));

