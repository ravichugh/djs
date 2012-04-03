var A = 1;
var B = 23;

var foo = function() /*: [[]] -> Int */ { return A + B; };

var i = foo();
assert (typeof i == "number");

var C = 17;

var bar = function() /*: [[]] -> Int */ { return C + foo() + A; };

var j = bar();
assert (typeof j == "number");
