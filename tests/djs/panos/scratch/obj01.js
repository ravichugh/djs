var foo = function(s, h) 
  /*: (s:Str, h: Ref) / (h: { f: () -> Top, _: Bot}  > lObjPro)-> Top  / sameType */ 
{
  var func = h[s];

  if (typeof func  === 'function') {
    assert(/*: {(= (tag v) "function")}  */  (func));
    assert(/*: () -> Top  */  (func));

    func();
  }

};
