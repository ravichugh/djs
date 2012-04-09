/*: #define tyPassenger
    {Dict|(and (not (has v "hasOwnProperty"))
               (implies (has v "weight") ((sel v "weight") : Num)))} */ "#define";

/*: [~lPass |-> (tyPassenger, lObjectProto)] */ "#weak";

var readWeight = function(p) /*:
    [[p:Ref(~lPass)]]
  / [~lPass |-> frzn,
     lObjectProto |-> (_:{Dict|(= (sel v "hasOwnProperty")
                                ____ObjectProto_hasOwnProperty)}, lROOT)]
 -> Num / same */
{
  var n = 300;
  /*: p lThaw1 */ "#thaw";
  if (p.hasOwnProperty("weight")) { n = p.weight; }
  /*: p (~lPass, thwd lThaw1) */ "#freeze";
  return n;
};
