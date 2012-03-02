
var x = /*: lx */ {f:0, g:"hi"};

/*: {(= v "hi")} */
(x.g); // Look, ma, no location params!  

x.g = "hello";

/*: {(= v "hello")} */
(x.g);

var b = x.hasOwnProperty("f")
        && x.hasOwnProperty("g")
        && !(x.hasOwnProperty("h"));

/*: {(= v True)} */ b;

