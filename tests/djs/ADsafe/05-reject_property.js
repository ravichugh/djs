var reject_property = function(object, name1) 
  //TODO: commenting expressive type for speed
  /* (object: Top, name1: Str) / (lBanned: tyBanned) -> 
     { (implies  (falsy v)
     (and 
     (not (= name1 "arguments"))
     (not (= name1 "callee"))
     (not (= name1 "caller"))
     (not (= name1 "constructor"))
     (not (= name1 "prototype"))
     (not (= name1 "stack"))
     (not (= name1 "eval"))
     (not (= name1 "unwatch"))
     (not (= name1 "valueOf"))
     (not (= name1 "watch"))
     )) }  
     / sameExact */
  /*: (object: Top, name1: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */
{
  return typeof object !== 'object' || reject_name(name1);
};

