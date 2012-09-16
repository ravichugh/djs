var i = 1;
var j /*: Int */ = 0;
var f = function () /*: () -> Top */ {
  j += i;
};
f();
assert (/*: Int */ (j + i + 2));
