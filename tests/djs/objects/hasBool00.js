var hasBool = function(obj) /*: [;LL1,LL2;Heap]
    (obj:Ref(LL1))
  / Heap + 
    (LL1 |-> _:{Dict|(implies (objhas v "f" Heap LL2)
                              (Bool (objsel v "f" Heap LL2)))} > LL2)
 -> Top / same */
{
  if ("f" in obj) {
    assert (typeof obj.f === "boolean");
    assert ((obj.f === true) || (obj.f === false));
  }
};
