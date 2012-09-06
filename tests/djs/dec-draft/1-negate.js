var negate = function(x) /*: (x:NumOrBool) -> {(= (tag v) (tag x))} */ {
  if (typeof(x) == "number") {
    return 0 - x;
  } else {
    return !x;
  }
};

assert (typeof (negate(1)) == "number");
assert (typeof (negate(true)) == "boolean");
