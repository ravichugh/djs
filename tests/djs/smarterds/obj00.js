var foo = function(obj)
/*: [;L] [[obj:Ref(L)]]
       / [L |-> (d:{Dict|((sel v "f") : Num)}, lObjectProto)]
      -> Top / sameType */ {
  while (true) {
    1 + obj.f;
  }
};
