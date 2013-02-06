
// Simplified version of goog.typeOf(), which wraps the typeof operator to
// return "null" and "array" instead of "object".
//
// http://closure-library.googlecode.com/svn/docs/closure_goog_base.js.source.html#line631
//
// Ideally, we would use (value instanceof Array) to determine if
// Array.prototype is _somewhere_ in the prototype chain of value,
// but System !D does not currently expose a primitive operation for
// walking the __proto__ links of an object (though it could).
//
// Instead, we simulate this in a brittle way by writing the field
// "__hack__" into Array.prototype and then checking for the presence
// of "__hack__". This approach breaks if the prototype chain of an object
// contains "__hack__", or if an array literal does not have Array.prototype
// as its prototype (and its prototype chain does not contain "__hack__").

//Array.prototype.__hack__ = "dummy";

/*: #define tyScalar
    {(or (= (tag v) "number") (= (tag v) "boolean") (= (tag v) "string")
         (= (tag v) "undefined") (= v null))} */ "#define";

/*: #define ty1
    (v :: (value:tyScalar)
       -> {(ite (= value null) (= v "null") (= v (tag value)))}) */ "#define";

/*: #define ty2
    (v :: [;L1,L2;]
          (value:Ref(L1)) / (L1 : x:Dict > L2)
       -> {(ite (objhas x "__hack__" cur L2) (= v "array") (= v "object"))}
        / same) */ "#define";

/*: #define ty3
    (v :: [A;L1,L2;]
          (value:Ref(L1)) / (L1 : Arr(A) > L2)
       -> {(ite (heaphas cur L2 "__hack__") (= v "array") (= v "object"))}
        / same) */ "#define";

//var typeOf = function(value) /*: {(and ty1 ty2 ty3)} */
var typeOf = function(value) /*: {ty1} */
{
  var s = typeof value;
  if (s == 'object') {
    if (value) { return ("__hack__" in value) ? 'array' : 'object'; }
    else       { return 'null'; }
  }
  return s;
};

// /*: {(= v "number")} */ (typeOf(1));
// /*: {(= v "string")} */ (typeOf("hi"));
// /*: {(= v "boolean")} */ (typeOf(true));
// /*: {(= v "null")} */ (typeOf(null));
// /*: {(= v "object")} */ (typeOf({}));
// /*: {(= v "array")} */ (typeOf([]));
// /*: {(= v "undefined")} */ (typeOf(undefined));
