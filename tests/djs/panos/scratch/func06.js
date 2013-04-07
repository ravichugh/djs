var s = /*: ls */  {};

s.set = function(a) 
/*: (() -> Num) / (ls: Dict > lObjPro) -> Top / sameType */
{ 
  s.f = a; 
};

var ff = function() /*: () -> Num */ { return(999); };


s.set(ff);

//print(s.f());
