var foo = function(s, h) 
  /*: (s:{(or (= v "f") (= v "g") )}, h: Ref)
    / (h: {Dict|(and (dom v {"f", "g"})
                     (Str (sel v "f"))
                     (Str (sel v "g"))
                     (= (tag (sel v "f")) "string")
                     (= (tag (sel v "g")) "string")
                )} > lObjPro,
       lObjPro: {_:Bot} > lROOT)
   -> Top / sameType */ 

{
  assert(/*: Str */ (h[s]));

};
