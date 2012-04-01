var x = /*: lx */ {};
var k = "blah";

/*: [Heap]
      [Heap ++
       &x |-> _:Ref(lx),
       &k |-> kk:Str,
       lx |-> (_:{Dict|(implies (objhas v kk Heap lObjectProto)
                               ((objsel v kk Heap lObjectProto) : Bool))}, lObjectProto)
      ] -> Top / sameType */
for (k in x) {
  // assert ((x[k] == true) || (x[k] == false));
  0;
}
