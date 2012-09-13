/*: -augmentHeaps false */ "#options";

/*: #define ty_toNum (x:Top) -> Num */ '#define';

var toNum = function(x) /*: ty_toNum */ {
  if (typeof(x) == "number")       { return x; }
  else if (typeof(x) == "boolean") { return x ? 1 : 0; }
  else                             { return -1; }
};

/*: #define ty_getCount
    [;Lt,Ltp;] (t:Ref(Lt), c:Str)
             / (Lt |-> _:Dict > Ltp, &toNum |-> _:ty_toNum)
            -> Num / same */ '#define';

var getCount = function(t,c) /*: ty_getCount */ {
  if (c in t) {
    return toNum(t[c]);
  } else {
    return 0;
  }
};

/*: #define ty_incCount
    [;Lt,Ltp;] (t:Ref(Lt), c:Str)
             / (Lt |-> dt:Dict > Ltp,
                &toNum |-> blah1:ty_toNum,
                &getCount |-> blah2:ty_getCount)
            -> Top
             / (Lt |-> _:{(and (eqmod v dt {c}) (Num (sel v c)))} > Ltp,
                &toNum |-> same,
                &getCount |-> same) */ "#define";

var incCount = function(t,c) /*: ty_incCount */ {
  var i = getCount(t,c);
  t[c] = 1 + i;
};
