var x = {f: 10};
var y = {g: 10};
var f = function () /*: () -> Int */ {
  return x.f + y.g;
};
assert (/*: Int */ (x.f));
assert (/*: Int */ (y.g));
