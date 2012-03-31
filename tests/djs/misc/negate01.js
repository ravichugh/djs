var negate = function(x) /*: [[x:Top]] -> {(ite (x:Num) (v:Num) (v:Bool))} */ {
  x = (typeof(x) == "number") ? 0 - x : !x;
  return x;
};

assert (typeof (negate(1)) == "number");
assert (typeof (negate(true)) == "boolean");
assert (typeof (negate(null)) == "boolean");
