var f = function (i) /*: (i:Int) -> Int */ {
  return 1 + i;
};
var g = function (i) /*: (i:Int) -> Int */ {
  return 1 + f(i);
};
var h = function (i) /*: (i:Int) -> Int */ {
  return 1 + g(i);
};
