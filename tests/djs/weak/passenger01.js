/*: #define tyPassenger
    {Dict|(implies (has v "weight") ((sel v "weight") : Num))} */ "#define";

/*: [~lPass |-> (tyPassenger, lObjectProto)] */ "#weak";

var readWeight = function(p) /*:
    [[p:Ref(~lPass)]]
  / [~lPass |-> frzn, lObjectProto |-> (_:{Dict|(not (has v "weight"))}, lROOT)]
 -> Num / same */
{
  var n = 300;
  /*: p lThaw1 */ "#thaw";
  if (p.weight) { n = p.weight; }
  /*: p (~lPass, thwd lThaw1) */ "#freeze";
  return n;
};
