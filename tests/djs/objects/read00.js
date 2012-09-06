var read = function(x,f)
  /*: [;L,L2;H] (x:Ref(L), f:Str)
              / H + (L |-> cx:{Dict|(objhas [v] f H L2)} > L2)
             -> {(= v (objsel [cx] f H L2))}
              / same */ {
  return x[f];
};

assert (read({a:1},"a") == 1);
assert (read({b:true},"b") == true);
