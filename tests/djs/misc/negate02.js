var negate = function(x) /*: (x:Top) -> {(ite (Num x) (Num v) (Bool v))} */ {
  if (typeof(x) == "number") { return 0 - x; }
  else                       { return !x;    }
};

assert (typeof (negate(1)) == "number");
assert (typeof (negate(true)) == "boolean");
assert (typeof (negate(null)) == "boolean");
