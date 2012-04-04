
/*: #define tyFoo {Dict|(and (dom v {"f"}) ((sel v "f") : Int))} */ "#define";

/*: #define ctorFoo
    [;Lnew] [[this:Ref(Lnew)]] / [Lnew |-> (_:Empty, lFooProto)]
         -> {(= v this)} / [Lnew |-> (_:tyFoo, lFooProto)] */ "#define";

function Foo() /*: new ctorFoo */ {
  this.f = 1;
  return this;
}

var wrapFoo = function()
/*: [;L] [[]]
       / [lFooObj |-> (_:{Dict|
            (and ((sel v "code") : ctorFoo)
                 ((sel v "prototype") : Ref(lFooProto)))}, lFunctionProto),
          lFooProto |-> (_:Dict, lObjectProto)]
      -> Ref(L)
       / [L |-> (_:tyFoo, lFooProto),
          lFooObj |-> sameExact,
          lFooProto |-> sameExact] */
{
  return new /*: [;L] lFooProto */ Foo();
};
