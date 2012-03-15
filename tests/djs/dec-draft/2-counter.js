/*: #define ty_toNum [[x:Top]] -> Int */ '#define';

// TODO think about restructuring js_typeof...

var toNum = function(x) /*: ty_toNum */ {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

/*: #define ty_getCount
    [;Lt;] [[t:Ref(Lt), c:Str]]
         / [Lt |-> dt:Dict, &toNum |-> blah:ty_toNum]
        -> Int / same */ '#define';

var getCount = function(t,c) /*: ty_getCount */ {
  if (c in t) {
    return toNum(t[c]);
  } else {
    return 0;
  }
};

/*: #define ty_incCount
    [;Lt;] [[t:Ref(Lt), c:Str]]
         / [Lt |-> dt:Dict,
            &toNum |-> blah1:ty_toNum,
            &getCount |-> blah2:ty_getCount]
        -> Top
         / [Lt |-> dt2:{(and (eqmod v dt {c}) ((sel v c) : Int))},
            &toNum |-> same,
            &getCount |-> same] */ "#define";

var incCount = function(t,c) /*: ty_incCount */ {
  var i = /*: [;Lt;] */ getCount(t,c);
  t[c] = 1 + i;
};
