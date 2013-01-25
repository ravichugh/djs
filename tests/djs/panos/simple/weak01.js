/*: (~lNList: { Arr(Ref(~lNode)) | (packed v) }  > lArrPro) */ "#weak";
/*: (~lNode: { childNodes : Ref(~lNList) } > lObjPro) */ "#weak";

var foo = function (list) /*: (list: Ref(~lNList)) -> Top  */
{
//  var nodes = node.childNode
  
  var i /*: {Int | (>= v 0)} */ = 0 ;
  /*:  list  lNList0 */ "#thaw";
  var len = list.length;
  var b = i < len; 
  /*: list (~lNList, thwd lNList0) */ "#freeze";

  /*: (&list: Ref(~lNList), &b : Bool, &len: Int) -> sameType */ 
  for (i = 0; b; i += 1) {
    /*:  list  lNList2 */ "#thaw";
    len = list.length;
    b = i < len;
    list[i];
    /*: list (~lNList, thwd lNList2) */ "#freeze";
  }


};
