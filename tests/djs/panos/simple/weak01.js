/*: (~lNList: { Arr(Ref(~lNode)) | (packed v) }  > lArrPro) */ "#weak";
/*: (~lNode: { list : Ref(~lNList), n : Int } > lObjPro) */ "#weak";

var foo = function (node) /*: (node: Ref(~lNode)) -> Ref(~lNode)  */
{
  var l = node.list;
  var s = node;
  
  var i = 0 ;
  /*:  l  lNList0 */ "#thaw";
  var len = l.length;
  var b = i < len; 
  /*: l (~lNList, thwd lNList0) */ "#freeze";

  /*: (&i: i0: {Int | (>= v 0)}, 
      &l: Ref(~lNList), 
      &b : Bool, 
      &len: Int, 
      &s: {(or (v::Ref(~lNode)))}) 
      -> sameType */ 
  for (i = 0; b; i += 1) {
    /*:  l lNList2 */ "#thaw";
    b = i < l.length;
    if (b) s = l[i];
    /*: l (~lNList, thwd lNList2) */ "#freeze";
  }

  return s;

};
