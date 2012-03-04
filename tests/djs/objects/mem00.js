var x = {};
x.f = undefined;
/*: {(= v true )} */ ("f" in x);
