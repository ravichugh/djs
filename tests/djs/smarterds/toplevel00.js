var A = 1;
var B = 23;

var foo = function() /*: [[]] -> Int */ { return A + B; };

var i = foo();
assert (typeof i == "number");
