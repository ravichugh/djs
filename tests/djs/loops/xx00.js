var i = 0;
/*: [H] [H ++ &i|->n:Int] ->
    Top / [H ++ &i|->m:{Int|(ite (< n 10) (= v 10) (= v n))}] */
while (i < 10) {
  i = i + 2; // incrementing by 2 breaks the desired invariant
};
/*: {(= v 10)} */ (i);
