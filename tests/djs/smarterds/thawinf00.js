/*: #define tyFoo {Dict|(and ((sel v "n") : Int) ((sel v "m") : Int))} */ "#define";

/*: [~lFoo |-> (tyFoo, lFooProto)] */ "#weak";

var bar = function(o) /*: [[o:Ref(~lFoo)]] -> Int */ {
  o.n;
  o.m;
  o.n;
  return o.n + o.m;
};
