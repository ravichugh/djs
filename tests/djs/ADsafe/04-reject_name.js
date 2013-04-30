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


var reject_name = function (name_) 
  /*: (name_: Str) -> { (implies  (falsy v)
                          (and 
                             (not (= name_ "arguments"   ))
                             (not (= name_ "callee"      ))
                             (not (= name_ "caller"      ))
                             (not (= name_ "constructor" ))
                             (not (= name_ "prototype"   ))
                             (not (= name_ "stack"       ))
                             (not (= name_ "eval"        ))
                             (not (= name_ "unwatch"     ))
                             (not (= name_ "valueOf"     ))
                             (not (= name_ "watch"       ))
                          )) }  */
{  
  return 
    typeof name_ !== 'number' 
    && (
        typeof name_ !== 'string' 
        || banned[name_] 
        || name_.charAt(0) === '_' 
        || name_.slice(-1, 0) === '_' //PV: added 2nd argument to slice
       );
};

