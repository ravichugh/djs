var x = {};
x.f = undefined;
assert (/*: {(= v true )} */ ("f" in x));
