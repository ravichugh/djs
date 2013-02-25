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


var reject_name = /*: (name_: Str) -> { (implies  (falsy v)
                          (and 
                             (not (= name_ "arguments"))
                             (not (= name_ "callee"))
                             (not (= name_ "caller"))
                             (not (= name_ "constructor"))
                             (not (= name_ "prototype"))
                             (not (= name_ "stack"))
                             (not (= name_ "eval"))
                             (not (= name_ "unwatch"))
                             (not (= name_ "valueOf"))
                             (not (= name_ "watch"))
                             )) }  */ "#extern";


var reject_property = function(object, name_) 
  /*: (object: Top, name_: Str) -> 
     { (implies  (falsy v)
     (and 
       (not (= name_ "arguments"))
       (not (= name_ "callee"))
       (not (= name_ "caller"))
       (not (= name_ "constructor"))
       (not (= name_ "prototype"))
       (not (= name_ "stack"))
       (not (= name_ "eval"))
       (not (= name_ "unwatch"))
       (not (= name_ "valueOf"))
       (not (= name_ "watch"))
     )) } */
  /* (object: Top, name_: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */
{
  return typeof object !== 'object' || reject_name(name_);
};

