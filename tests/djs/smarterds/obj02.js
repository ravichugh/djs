var foo = function(obj)
/*: [;L] [[obj:Ref(L)]]
       / [L |-> (d:{Dict|(and (dom v {"f","g"})
                              ((sel v "f") : Num)
                              ((sel v "g") : Num))}, lObjectProto)]
      -> Top / sameType */ {
  while (true) {
    obj.f = 1 + obj.f;
    obj.g = 2;
  }
};
