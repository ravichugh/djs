var dispatch = function(x,f)
/*: [A,B;Lx;] [[x:Ref(Lx), f:Str]]
            / [Lx |-> dx:{Dict|(and
                  (v :: A)
                  ((sel v f) :: [[_:Ref(Lx)]] / [Lx |-> blah:A] -> B / same))}]
           -> B / same */ {
  var fn = x[f];
  return fn(x);
};
