var b = false;

/*: (&b |-> x1:Bool)
 -> (&b |-> x2:{(= v true)}) */
while (!b) { b = !b; }

assert (b == true);
