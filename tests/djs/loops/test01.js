var i = 0;
/*: (&i: n:Int) -> (&i: {Int|(ite (< n 10) (= v 10) (= v n))}) */
while (i < 10) {
  i = i + 1;
};
assert (i == 10);
