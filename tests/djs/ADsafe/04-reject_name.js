var reject_name = function (name1) 
  //TODO: commenting expressive type for speed
  /* (name1: Str) / (lBanned: tyBanned) -> 
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

  /*: (name1: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */
{  
  return 
    typeof name1 !== 'number' 
    && (
        typeof name1 !== 'string' 
        || banned[name1] 
        || name1.charAt(0) === '_' 
        || name1.slice(-1, 0) === '_' //PV: added 2nd argument to slice
       );
};

