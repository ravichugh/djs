//TODO: prove the last assertion

var s = /*: ls */  {};

var id = 0;

s.set = function(a) 
/*: (() / (ls: Dict > lObjPro, &id:idv:Num) -> {(= v idv)} / sameType) / (ls: Dict > lObjPro, &id:idv:Num) 
    -> Num / (ls: { f: () / (ls: Dict > lObjPro, &id:Num) -> Num / sameType} > lObjPro) */
{ 
  s.f = a; 
  return 999;
};

var ff = function() /*: () / (ls: Dict > lObjPro, &id:idv:Num) -> {(= v idv)} / sameType*/  { return(id); };

id = s.set(ff);

assert(/*: () / (ls: Dict > lObjPro)-> Num / sameType */  (s.f));

//assert(s.f() === 999);

//print(s.f());
