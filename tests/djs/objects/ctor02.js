
// notice that this constructor doesn't explicitly name H because
// it doesn't mention and Obj* symbols.
// though, of course, a prefix heap var will be added by parser.

/*: #define tyGetName
    [;Lthis,Lpro;HH]
       [[this:Ref(Lthis)]]
     / [HH ++ Lthis |-> (innerDThis:{Dict|
          (and (objhas [v] "name" [HH] Lpro)
              ((objsel [v] "name" [HH] Lpro) : Str))}, Lpro)]
    -> {(= v (objsel [innerDThis] "name" [HH] Lpro))}
     / same
*/ "#define";

function Foo(name)
/*: new [;Lthis;]
        [[this:Ref(Lthis), name:Str]]
      / [Lthis |-> (dThis:{(= v empty)}, &Foo_proto)]
     -> Ref(Lthis)
      / [Lthis |-> (dThis2:{Dict|
           (and (dom v {"name","getName"})
                (= (sel v "name") name)
                ((sel v "getName") :: tyGetName)
           )}, &Foo_proto)] */
{
  this.name = name;

  this.getName = function() /*: tyGetName */ { return this.name; };

  return this;
}

var bob = new /*: [;lBob;] &Foo_proto */ Foo("bob");

/*: {(= v "bob")} */ (bob.name);
/*: {(= v "bob")} */ (bob.getName());
