var s = /*: ls */  {};

var id = 0;

s.set = function(a) 
/*: (() / (ls: Dict > lObjPro) -> Num / sameType) / (ls: Dict > lObjPro) 
    -> Num / (ls: { f: () / (ls: Dict > lObjPro) -> Num / sameType} > lObjPro) */
{ 
  s.f = a; 
  return 999;
};

var ff = function() /*: () / (ls: Dict > lObjPro) -> Num / sameType*/  { return(id); };

id = s.set(ff);

assert(/*: () / (ls: Dict > lObjPro)-> Num / sameType */  (s.f));

//assert(s.f() === 999);

//print(s.f());
