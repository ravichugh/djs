var foo = function(s, h) 
  /*: (s:{(or (= v "f") (= v "g"))}, h: Ref)
    / (h: {Dict|(and (dom v {"f", "g"})
                     ((sel v "f") :: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType)
                     ((sel v "g") :: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType)
                     (= (tag (sel v "f")) "function")
                     (= (tag (sel v "g")) "function")
                )} > lObjPro,
       lObjPro: {_:Bot} > lROOT)
   -> Top / sameType */ 
{
//  assert(/*: () -> Top */ (h[s]));
  assert(/*: {(= (tag v) "function")} */ (h[s]));
  assert(/*: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType */ (h[s]));
};
