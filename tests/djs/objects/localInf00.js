
var x = {f:0, g:"hi"};

assert (x.g == "hi"); // Look, ma, no location params!  

x.g = "hello";

assert (x.g == "hello");

var b = x.hasOwnProperty("f")
        && x.hasOwnProperty("g")
        && !(x.hasOwnProperty("h"));

assert (b == true);

