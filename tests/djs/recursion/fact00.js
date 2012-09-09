// i modified the JS parser and translation to EJS
// to allow named function expressions

var factorial = function fact(n) /*: (Int) -> Int */ {
  return n <= 0 ? 1 : n * fact(-1);
};

assert (/*: Int */ (factorial(5)));
