/*: dispatch :: [A,B] (x:Ref, f:Str)
    / (x: {(and (= (tag v) "Dict") (v :: A)
           ((sel v f) :: (Ref(x)) / (x: A > x.pro) -> B / same))} > x.pro)
   -> B / same */ "#type";
var dispatch = function(x,f) {
  var fn = x[f];
  return fn(x);
};
