var banned = /*: lBanned */ {
      'arguments'     : true,
      callee          : true,
      caller          : true,
      constructor     : true,
      'eval'          : true,
      prototype       : true,
      stack           : true,
      unwatch         : true,
      valueOf         : true,
      watch           : true
    };


var reject_name = function (name1) 
  /*: (name1: Str) -> { (implies  (falsy v)
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
                             )) }  */
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

