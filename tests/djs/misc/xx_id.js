var id = function(x) /*: (x:Top) -> {(= v x)} */ {
  return x;
};

assert (id(1) == 1);
assert (id(true) == false);
