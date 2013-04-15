//DJS cannot TC because s is not declared in the body of function set.

var id = 0;

var s = /*: ls */ {
  set: function(a) 
    /*: (() -> Num) / (ls: Dict > lObjPro) -> Top / sameType */
    { 
      s.f = a; 
      return 999;
    }
};

var ff = function() /*: () -> Num */ { return(id); };

id = s.set(ff);

print(s.f());
