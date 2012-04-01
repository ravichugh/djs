var negate = function(x) /*: [[x:NumOrBool]] -> {(ite (x:Num) (v:Num) (v:Bool))} */ {
  if (typeof(x) == "number") { x = 0 - x; }
  else                       { x = !x;    }
  return x;
};

assert (typeof (negate(1)) == "number");
assert (typeof (negate(true)) == "boolean");
