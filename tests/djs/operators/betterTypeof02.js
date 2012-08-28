/*: #define tyScalar
    {(or (= (tag v) "number") (= (tag v) "boolean") (= (tag v) "string")
         (= (tag v) "undefined") (= v null))} */ "#define";

var typeOf =
/*: {(and
       (v :: [[value:tyScalar]]
          -> {(ite (= value null) (= v "null") (= v (tag value)))})

       (v :: [;L1,L2;H]
             [[value:Ref(L1)]] / [H ++ L1 |-> (x:Dict, L2)]
          -> {(ite (objhas x "__hack__" H L2) (= v "array") (= v "object"))}
           / same)

       (v :: [A;L1,L2;H]
             [[value:Ref(L1)]] / [H ++ L1 |-> (_:Arr(A), L2)]
          -> {(ite (heaphas H L2 "__hack__") (= v "array") (= v "object"))}
           / same)
     )}
*/ "#extern";

Array.prototype.__hack__ = "dummy";

assert ("number" == typeOf(1));
assert ("string" == typeOf("hi"));
assert ("boolean" == typeOf(true));
assert ("undefined" == typeOf(undefined));
assert ("null" == typeOf(null));
assert ("object" == typeOf({}));
assert ("array" == typeOf([]));
