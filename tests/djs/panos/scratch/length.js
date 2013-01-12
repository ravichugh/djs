var a = [10];

assert(/*: Int */ (a.length));

var b = "a";
assert(/*: Str */ (b));
assert(/*: Int */ (b.length));
assert(/*: Str */ (b.charAt(1)));

