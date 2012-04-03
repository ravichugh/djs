var foo = function()
/*: [;L] [[this:Ref(L)]]
       / [L |-> (d:{Dict|(and (dom v {"f","g"})
                              ((sel v "f") : Num)
                              ((sel v "g") : Num))}, lObjectProto)]
      -> Top / sameType */ {
  while (true) {
    this.f = 1 + this.f;
    this.g = 2;
  }
};
