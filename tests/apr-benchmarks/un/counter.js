var toNum = function(x) {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

var getCount = function(t,c) {
  if (c in t) {
    return toNum(t[c]);
  } else {
    return 0;
  }
};

var incCount = function(t,c) {
  var i = getCount(t,c);
  t[c] = 1 + i;
};
