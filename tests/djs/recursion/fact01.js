var factorial = function fact(n) /*: [[n:INT]] -> INT */ {
  if (n < 0) { return 1; }
  else       { return n * fact(n-1); }
};

/*: Int */ (factorial(5));
