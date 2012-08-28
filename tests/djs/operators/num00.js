assert (/*: {(and (= (tag v) "number") (integer v))} */ (1));

assert (/*: {(= v 2)} */ (2));

assert (/*: {(= v 3)} */ (1 + 2));

assert (/*: {(and (= (tag v) "number") (integer v))} */ (1 + 2));
