var x = {f: 10};
var y = /*: {Dict|(and (dom v {"g"}) (Int (sel v "g")))} */ {g: 10};
var f = function () /*: () -> Int */ {
  y.g += x.f;
  return y.g;
};
assert (/*: Int */ (x.f));
assert (/*: Int */ (y.g));
