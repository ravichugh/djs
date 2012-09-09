var i = 0;
/*: (&i: Int) -> (&i: Int) */
while (i < 10) {
  i = i + 1;
};
assert (/*: Int */ i);
