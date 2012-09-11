var toNum = function(x) /*: (Top) -> Num */ {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

assert (typeof toNum(1) == "number");
assert (typeof toNum(null) == "number");
