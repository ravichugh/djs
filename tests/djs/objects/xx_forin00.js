var x = /*: lx */ {};
var k;

/*: [Heap]
      [Heap ++
       &x |-> _:Ref(lx),
       &k |-> kk:Str,
       lx |-> (d:{Dict|(implies (objhas v kk Heap lObjectProto)
                               ((objsel v kk Heap lObjectProto) : Bool))}, lObjectProto)
      ] -> Top / sameType */
for (k in x) {
  // BAD: the annotation is a _forall_ property, so recursive call won't type check
}
