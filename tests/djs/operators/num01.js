assert (/*: {(and (= (tag v) "number"))} */ (1.0));

assert (/*: {(and (= (tag v) "number"))} */ (1.0 + 2.0));

assert (/*: {(and (= (tag v) "number"))} */ (1.0 + 2));

assert (/*: Num */ (1.0 + 2));
