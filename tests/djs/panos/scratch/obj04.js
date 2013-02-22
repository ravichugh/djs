var foo = function(s, h) 
  /*: (s:{(or (= v "f") (= v "g"))}, h: Ref)
    / (h: {Dict|(and (dom v {"f", "g"})
                     ((sel v "f") :: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType)
                     ((sel v "g") :: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType)
                )} > lObjPro,
       lObjPro: {_:Bot} > lROOT)
   -> Top / sameType */ 
{
//  assert(/*: () -> Top */ (h[s]));
  assert(/*: {(= (tag v) "function")} */ (h[s]));
//rkc TODO fix
//  assert(/*: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType */ (h[s]));
};
