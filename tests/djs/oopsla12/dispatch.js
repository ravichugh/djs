/*: dispatch :: [A,B;L1,L2;]
      (Ref(L1), f:Str) / (L1: {(and (= (tag v) "Dict") (v :: A)
                               ((sel v f) :: (Ref(L1)) / (L1: A > L2) -> B / same))} > L2)
   -> B / same */ "#type";
var dispatch = function(x,f) {
  var fn = x[f];
  return fn(x);
};
