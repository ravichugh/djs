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


var reject_name = /*: (name1: Str) -> { (implies  (falsy v)
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
                             )) }  */ "#extern";


var reject_property = function(object, name1) 
  /*: (object: Top, name1: Str) -> 
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
     )) } */
  /* (object: Top, name1: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */
{
  return typeof object !== 'object' || reject_name(name1);
};

