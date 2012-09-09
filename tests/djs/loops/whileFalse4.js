var foo = function(b) /*: (b:Bool) -> {(= v true)} */ {
  /*: (&b |-> a1:Bool) -> (&b |-> a2:{(= v true)}) */
  for (; !b; b = !b);
  return b;
};

assert (true == foo(true));
assert (true == foo(false));
