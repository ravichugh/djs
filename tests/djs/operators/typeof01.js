/*: #define tyScalar
    {(or (= (tag v) "number")
         (= (tag v) "boolean")
         (= (tag v) "string")
         (= (tag v) "undefined")
         (= v null))} */ "#define";

/*: #define tagSet
    {(or (= v "number")
         (= v "boolean")
         (= v "string")
         (= v "undefined")
         (= v "object"))} */ "#define";

var typeofScalar = function(x) /*: (x:tyScalar) -> tagSet */ {
  return typeof x;
};
