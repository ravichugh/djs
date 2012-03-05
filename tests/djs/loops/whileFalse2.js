var foo = function(b) /*: [[b:Bool]] -> {(= v true)} */ {
  /*: [&b |-> x1:Bool]
   -> [&b |-> x2:{(= v true)}] */
  while (!b) { b = !b; }
  return b;
};

/*: {(= v true)} */ (foo(true));
/*: {(= v true)} */ (foo(false));
