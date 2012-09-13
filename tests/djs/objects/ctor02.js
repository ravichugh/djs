
// notice that this constructor doesn't explicitly name H because
// it doesn't mention and Obj* symbols.
// though, of course, a prefix heap var will be added by parser.

/*: #define tyGetName
    [;Lthis,Lpro;HH]
       (this:Ref(Lthis))
     / HH + (Lthis |-> innerDThis:{Dict|
          (and (objhas [v] "name" HH Lpro)
               (Str (objsel [v] "name" HH Lpro)))} > Lpro)
    -> {(= v (objsel [innerDThis] "name" HH Lpro))}
     / same
*/ "#define";

function Foo(name)
/*: new [;Lthis;]
        (this:Ref(Lthis), name:Str)
      / (Lthis |-> dThis:{(= v empty)} > lFooProto)
     -> Ref(Lthis)
      / (Lthis |-> dThis2:{Dict|
           (and (dom v {"name","getName"})
                (= (sel v "name") name)
                ((sel v "getName") :: tyGetName)
           )} > lFooProto) */
{
  this.name = name;

  this.getName = function() /*: tyGetName */ { return this.name; };

  return this;
}

var bob = new /*: lBob > lFooProto */ Foo("bob");

assert (bob.name == "bob");
assert (bob.getName() == "bob");
