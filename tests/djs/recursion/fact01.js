var factorial = function fact(n) /*: (n:Int) -> Int */ {
  if (n < 0) { return 1; }
  else       { return n * fact(n-1); }
};

assert (/*: Int */ (factorial(5)));
