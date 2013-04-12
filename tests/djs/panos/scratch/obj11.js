//TODO
var obj = /*: l */ {
  foo:  function() /*: () -> Top */ { },

  bar:  function() /*: () / (l: { foo: () -> Top} > lObjPro) -> Top / sameType */ {
    //assert(/*: () / (l:t0) -> Top / sameType */ (obj.foo));
    this.foo();
  }
//,
//  baz:  function() /*: () -> Top */ {
//    this.bar();
//    this.foo();
//  }
};
