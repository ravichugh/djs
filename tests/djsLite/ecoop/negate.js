var negate = function(x) /*: [[x:IntOrBool]] -> {(= (tag v) (tag x))} */ {
  if (typeof(x) == "number") {
    return 0 - x;
  } else {
    return !x;
  }
};
