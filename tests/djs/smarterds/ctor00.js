
/*: #define tyFoo {Dict|(and (dom v {"f"}) ((sel v "f") : Int))} */ "#define";

/*: #define ctorFoo
    [;Lnew] [[this:Ref(Lnew)]] / [Lnew |-> (_:Empty, lFooProto)]
         -> {(= v this)} / [Lnew |-> (_:tyFoo, lFooProto)] */ "#define";

function Foo() /*: new ctorFoo */ {
  this.f = 1;
  return this;
}

var obj = new /*: [;lobj] lFooProto */ Foo();

Foo.prototype.g = /*: Int */ 10;

//// omitting the following from tyBar
////   lFooProto |-> (_:{Dict|((sel v "g") : Int)}, lObjectProto)

//// TODO: i'm _not_ threading through prototype objects right now,
//// because need to change macros as a pre-pass to expanding them
//// more delayed, and then storing the delayed expansion, not the
//// eager pre-pass one like currently

/*: #define tyBar
    [;L] [[this:Ref(L)]] / [L |-> (_:tyFoo, lFooProto)]
      -> Int / sameExact */ "#define";

Foo.prototype.bar = function() /*: tyBar */ {
  return 1 + this.f + this.g;
};

obj.bar();

var baz = function(foo)
/*: [;L] [[foo:Ref(L)]]
       / [L |-> (_:tyFoo, lFooProto),
          lFooProto |-> (_:{Dict|(and ((sel v "g") : Int)
                                      ((sel v "bar") : tyBar))}, lObjectProto)]
      -> Int / sameExact */
{
  return 1 + foo.bar();
};

baz(obj);
