var foo =  "#extern";

var bar = function(k) 
/*: [;L; ](k: {(or (= v "keya") (= v "keyb") )}) / (&foo: Ref(L), L: { keya: Str, keyb: Str, _: Bot  } > lObjPro) -> Top / sameType*/
{
  //assert(/*: {keya: Str, keyb: Str, _: Bot} */ (foo));
  assert(/*: NotUndef */ (foo[k]));

};
