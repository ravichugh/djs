
assert (/*: {(= v false)} */ (true && false));

assert (/*: {(= v 0)} */ (0 && false));

assert (/*: {(= v 2)} */ (1 && 2));

assert (/*: {(= v 0)} */ (0 && 2));

assert (/*: {(= v "")} */ ("" && 2));

assert (/*: {(= v 2)} */ ("hi" && 2));

assert (/*: {(= v null)} */ (null && 2));

