
// Simplified version of goog.typeOf(), which wraps the typeof operator to
// return "null" and "array" instead of "object".
//
// http://closure-library.googlecode.com/svn/docs/closure_goog_base.js.source.html#line631
//
// Instead of using         (value instanceof Array),
// we use the ES5 function  Array.isArray(value).

var typeOf = function(value)
/*: {(and

       (v :: [[value:{(or (= (tag v) "number") (= (tag v) "boolean")
                          (= (tag v) "string") (= (tag v) "undefined")
                          (= v null))}]]
          -> {(ite (= value null) (= v "null") (= v (tag value)))})

       (v :: [A;LL1,LL2;H] [[value:Ref(LL1)]]
           / [H ++ LL1 |-> (_:Arr(A), LL2),
              &Array |-> _:Ref(lArray),
              lArray |-> (_:{Dict|(= (sel v "isArray") ____isArray)}, lObjectProto)]
          -> {(= v "array")} / same)

       (v :: [;LL1,LL2;H] [[value:Ref(LL1)]]
           / [H ++ LL1 |-> (x:Dict, LL2),
              &Array |-> _:Ref(lArray),
              lArray |-> (_:{Dict|(= (sel v "isArray") ____isArray)}, lObjectProto)]
          -> {(= v "object")} / same)
)} */
{
  var s = typeof value;
  if (s == 'object') {
    if (value) { return (Array.isArray(value)) ? 'array' : 'object'; }
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
