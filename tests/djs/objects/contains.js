
var b = /*: lB */  { a: "1"};

var f = function(str) 
/*: (str: { Str | (not (= v null))}) / (lB : d: {a : {Str | (= v "1")} }  > lObjPro ) -> {(implies (falsy v) (not (= str "a")) )}  / sameExact */ 
{
  //assert(/*: {(implies (falsy v) (not (= str "a") )) }*/ (b[str]));
  //assert(/*: {(implies (= str "a") (truthy v)) }*/ (b[str]));
  return b[str];
};
