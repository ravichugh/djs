var foo = function(s, h) 
  /*: (s:Str, h: Ref)
    / (h: {Dict|(and (dom v {"f"})
                     ((sel v "f") :: () -> Top)
                     (= (tag (sel v "f")) "function"))} > lObjPro,
       lObjPro: {_:Bot} > lROOT)
   -> Top / sameType */ 
{
  var func = h[s];

  if (typeof func  === 'function') {
    assert (s == "f");
    assert(/*: {(= (tag v) "function")}  */  (func));
    assert(/*: () -> Top  */  (func));

    //func();
  }

};
