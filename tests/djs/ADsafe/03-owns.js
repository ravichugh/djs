var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

var owns = function(object, string) 
/*: [;L;](object: Ref(L), string: Str) / (L: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
    { (implies (= v true) (has d {string}))} / sameType */
{
  return 
    object &&
    (typeof object === 'object' &&
    //Object.prototype.hasOwnProperty.call(object, string_check(string));
    object.hasOwnProperty(string_check(string)));
};

