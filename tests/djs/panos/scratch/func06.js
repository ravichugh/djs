var s = /*: ls */  {};
var id = 0;

var s0 = /*: ls0 */ {
  set: function(a) 
  /*: ( ()/ (&s: Ref(ls0), ls0: Dict > lObjPro) -> Int / sameType ) / (&s: Ref(ls), ls: Dict > lObjPro) -> Int / sameType */
  {
    s.f = a; 
    return 999;
  }
};

s = s0;

var ff = function() /*: () / (&s: Ref(ls),  ls: Dict > lObjPro) -> Int / sameType */ { return(id); };
s.set(ff);
//assert(/*: Top  */ (s.set(ff)));
//id = s.set(ff);

//print(s.f());
