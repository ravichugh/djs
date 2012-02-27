/*: #define ty_toInt [[x:Top]] -> Int */ '#define';

var toInt = function(x) /*: ty_toInt */ {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

/*: #define ty_getCount
    [;Lt;] [[t:Ref(Lt), c:Str]]
         / [Lt |-> dt:Dict, &toInt |-> blah:ty_toInt]
        -> Int / same */ '#define';

var getCount = function(t,c) /*: ty_getCount */ {
  if (c in t) {
    return toInt(t[c]);
  } else {
    return 0;
  }
};

/*: #define ty_incCount
    [;Lt;] [[t:Ref(Lt), c:Str]]
         / [Lt |-> dt:Dict,
            &toInt |-> blah1:ty_toInt,
            &getCount |-> blah2:ty_getCount]
        -> Top
         / [Lt |-> dt2:{(and (eqmod v dt {c}) ((sel v c) : Int))},
            &toInt |-> same,
            &getCount |-> same] */ "#define";

var incCount = function(t,c) /*: ty_incCount */ {
  var i = /*: [;Lt;] */ getCount(t,c);
  t[c] = 1 + i;
};
