var dispatch = function(x,f)
/*: [A,B;L1,L2;]
    (x:Ref(L1), f:Str)
  / (L1 |-> _:{(and (= (tag v) "Dict")
                    (v :: A)
                    ((sel v f) :: (_:Ref(L1)) / (L1 |-> _:A > L2)
                               -> B / same))} > L2)
 -> B / same */
{
  var fn = x[f];
  return fn(x);
};
