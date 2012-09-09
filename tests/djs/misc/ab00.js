var A = 1;

var foo = function()
/*: () / (&A |-> _:Int) -> Int / (&A |-> _:Int) */
  { return A; };

var i = foo(); assert (typeof i == "number");

assert (typeof foo() == "number");
