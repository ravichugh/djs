var foo = function(ns)
/*: [;L] [[ns:Ref(L)]]
       / [L |-> (a:{(and (v::Arr(Int)) (packed v))}, lArrayProto)]
      -> Top / sameType */ {
  var i = 0;
  var size = ns.length;
  for (; i < size; i++) ns[i] + 1;
};
