var id = function(x) /*: (x:Top) -> {(= v x)} */ {
  return x;
};

assert (id(1) == 1);
assert (id(true) == true);
assert (id({f: 'yo'}.f) == 'yo');
assert (id({f: 'yo'}.f) != 'hey');
