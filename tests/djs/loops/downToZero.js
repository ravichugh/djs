/*: goalType {(ite (>= i 0) (= v (-1)) (= v i))} */ "#define";
/*: goalType0 {(ite (>= i0 0) (= v (-1)) (= v i0))} */ "#define";

// TODO: once macros are implemented, something like:
//   /*: type goalType(i) = {(ite (>= i 0) (= v (-1)) (= v i))} */ "#define";

var downToZero = function(i) /*: (i:Int) -> goalType */ {
  /*: (&i: i0:Int) -> (&i: goalType0) */
  while (i >= 0) {
    i--;
  }
  return i;
};

assert (downToZero( 2) == -1);
assert (downToZero( 1) == -1);
assert (downToZero( 0) == -1);
assert (downToZero(-1) == -1);
assert (downToZero(-2) == -2);
assert (downToZero(-3) == -3);
