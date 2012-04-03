var toNum = function(x) /*: [[x:Top]] -> Num */ {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

/*: #define ty_getCount [;Lt,Ltp;]
    [[t:Ref(Lt), c:Str]] / [Lt |-> (_:Dict, Ltp)] -> Num / same */ '#define';

var getCount = function(t,c) /*: ty_getCount */ {
  if (c in t) {
    return toNum(t[c]);
  } else {
    return 0;
  }
};

/*: #define ty_incCount [;Lt,Ltp;]
    [[t:Ref(Lt), c:Str]] / [Lt |-> (dt:Dict, Ltp)] -> Top
  / [Lt |-> (_:{(and (eqmod v dt {c}) ((sel v c) : Num))}, Ltp)] */ "#define";

var incCount = function(t,c) /*: ty_incCount */ {
  var i = getCount(t,c);
  t[c] = 1 + i;
};
