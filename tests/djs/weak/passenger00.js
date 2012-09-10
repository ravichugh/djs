/*: #define tyPassenger
    {Dict|(and (not (has v "hasOwnProperty"))
               (implies (has v "weight") (Num (sel v "weight"))))} */ "#define";

/*: (~lPass |-> tyPassenger > lObjPro) */ "#weak";

var readWeight = function(p) /*:
    (p:Ref(~lPass)) / (~lPass |-> frzn, lObjPro |-> {(= v theObjPro)} > lROOT)
 -> Num / same */
{
  var n = 300;
  /*: p lThaw1 */ "#thaw";
  if (p.hasOwnProperty("weight")) { n = p.weight; }
  /*: p (~lPass, thwd lThaw1) */ "#freeze";
  return n;
};
