var toNum = function(x) /*: (Top) -> Num */ {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

var getCount = function(t,c) /*: (t:Ref, Str) / (t: Dict > t.pro) -> Num / same */ {
  if (c in t) {
    return toNum(t[c]);
  } else {
    return 0;
  }
};

/*: incCount :: (t:Ref, c:Str) / (t: dt:Dict > t.pro)
             -> Top / (t: {(and (eqmod v dt {c}) (Num (sel v c)))} > t.pro) */ "#type";
var incCount = function(t,c) {
  var i = getCount(t,c);
  t[c] = 1 + i;
};
