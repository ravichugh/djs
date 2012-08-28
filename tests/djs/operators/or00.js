
assert (/*: {(= v true)} */ (true || false));

assert (/*: {(= v false)} */ (0 || false));

assert (/*: {(= v 1)} */ (1 || 2));

assert (/*: {(= v 2)} */ (0 || 2));

assert (/*: {(= v 2)} */ ("" || 2));

assert (/*: {(= v "hi")} */ ("hi" || 2));

assert (/*: {(= v 2)} */ (null || 2));

