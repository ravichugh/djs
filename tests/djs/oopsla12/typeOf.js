
var typeOf = function(value) /*: {(and
  (v :: [;LL1,LL2;H] [[value:Ref(LL1)]] / [H ++ LL1 |-> (_:Dict, LL2)]
     -> {(= v "object")} / same)
  (v :: [A;LL1,LL2;H] [[value:Ref(LL1)]] / [H ++ LL1 |-> (_:Arr(A), LL2)]
     -> {(= v "array")} / same)
  (v :: [[value:({(= (tag v) {"number","boolean","string","undefined"})})?]]
     -> {(ite (= value null) (= v "null") (= v (tag value)))}))} */
{
  var s = typeof value;
  if (s == 'object') {
    if (value) { return (isArray(value)) ? 'array' : 'object'; }
    else       { return 'null'; }
  }
  return s;
};

assert (typeOf(1) == "number");
assert (typeOf("hi") == "string");
assert (typeOf(true) == "boolean");
assert (typeOf(null) == "null");
assert (typeOf({}) == "object");
assert (typeOf([]) == "array");
assert (typeOf(undefined) == "undefined");
