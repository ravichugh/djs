/*: #define tyFoo {Dict|(and ((sel v "n") : Int) ((sel v "m") : Int))} */ "#define";

/*: [~lFoo |-> (tyFoo, lFooProto)] */ "#weak";

var bar = function(o) /*: [[o:Ref(~lFoo)]] -> Int */ {
  o.n = 1;
  o.m = 2;
  o.n = 3;
  return o.n + o.m;
};
