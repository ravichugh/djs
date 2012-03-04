var x = {};
/*: {(= v false )} */ ("f" in x);
/*: {(= v undefined)} */ (x.f);

x.f = undefined;
/*: {(= v true )} */ ("f" in x);
/*: {(= v undefined)} */ (x.f);
