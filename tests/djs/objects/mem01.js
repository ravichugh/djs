var x = {};
assert (/*: {(= v false )} */ ("f" in x));
assert (/*: {(= v undefined)} */ (x.f));

x.f = undefined;
assert (/*: {(= v true )} */ ("f" in x));
assert (/*: {(= v undefined)} */ (x.f));
