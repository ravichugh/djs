var i = 0, j;

/*: (&i: i0:Int, &j: {(or (< i0 10) (= v 17))})
 -> (&i: Int, &j: {(= v 17)}) */
while (i < 10) {
  j = 17;
  i++;
}
