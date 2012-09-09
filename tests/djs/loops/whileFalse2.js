var foo = function(b) /*: (b:Bool) -> {(= v true)} */ {
  /*: (&b |-> x1:Bool)
   -> (&b |-> x2:{(= v true)}) */
  while (!b) { b = !b; }
  return b;
};

assert (true == foo(true));
assert (true == foo(false));
