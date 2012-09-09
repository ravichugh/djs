var i = 0;
/*: (&i|->n:Int) ->
    (&i|->m:{Int|(ite (< n 10) (= v 10) (= v n))}) */
while (i < 10) {
  i = i + 2; // incrementing by 2 breaks the desired invariant
};
assert (i == 10);
