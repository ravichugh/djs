/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyBunch { "___nodes___": Ref(~lNodes), "___star___": Bool} */ "#define";

var star    /*: Bool */ = "#extern";
var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var purge_event_handlers = /*: (node: Ref(~lNode)) -> Top */ "#extern";

var replace = function (replacement)
/*: {(and
        (v:: (this: Ref(~lBunch), replacement: Ref(~lBunch)) -> Top )
        (v:: (this: Ref(~lBunch), replacement: Ref(~lBunchs)) -> Top )
        
    )} */
{
  reject_global(this);
  var b = this.___nodes___,
      flag = false,
      i /*: { Int | (>= v 0)} */ = 0,
      j,
      newnode,
      node /*: Ref(~lNode) */ = null,
      parent,
      rep;
  /*: b lNodes */ "#thaw";
  if (b.length === 0) {
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
    return;
  }
  else {
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }

  /*: b lNodes */ "#thaw";
  /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> sameType */ 
  for (i = 0; i < b.length; i += 1) {
    purge_event_handlers(b[i]);
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";



//
//  var rnodes = replacement.___nodes___;
//  /*: rnodes lNodes */ "#thaw";
//
//  if (!replacement || replacement.length === 0 ||
//      (rnodes &&
//       rnodes.length === 0)) 
//  {
//    /*: rnodes (~lNodes, thwd lNodes) */ "#freeze";
//
//    /*: b lNodes */ "#thaw";
//    /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
//      -> sameType */ 
//    for (i = 0; i < b.length; i += 1) {
//      node = b[i];
//      purge_event_handlers(node);
//      if (node.parentNode) {
//        node.parentNode.removeChild(node);
//      }
//    }
//    /*: b (~lNodes, thwd lNodes) */ "#freeze";
//  }
  //else if (isArray(replacement)) {
  //         if (replacement.length !== b.length) {
  //           error('ADsafe: Array length: ' +
  //               b.length + '-' + value.length);
  //         }
  //         for (i = 0; i < b.length; i += 1) {
  //           node = b[i];
  //           parent = node.parentNode;
  //           purge_event_handlers(node);
  //           if (parent) {
  //             rep = replacement[i].___nodes___;
  //             if (rep.length > 0) {
  //               newnode = rep[0];
  //               parent.replaceChild(newnode, node);
  //               for (j = 1; j < rep.length; j += 1) {
  //                 node = newnode;
  //                 newnode = rep[j];
  //                 parent.insertBefore(newnode, node.nextSibling);
  //               }
  //             } else {
  //               parent.removeChild(node);
  //             }
  //           }
  //         }
  //} 
  //else {
  //         rep = replacement.___nodes___;
  //         for (i = 0; i < b.length; i += 1) {
  //           node = b[i];
  //           purge_event_handlers(node);
  //           parent = node.parentNode;
  //           if (parent) {
  //             newnode = flag ? rep[0].cloneNode(true) : rep[0];
  //             parent.replaceChild(newnode, node);
  //             for (j = 1; j < rep.length; j += 1) {
  //               node = newnode;
  //               newnode = flag ? rep[j].clone(true) : rep[j];
  //               parent.insertBefore(newnode, node.nextSibling);
  //             }
  //             flag = true;
  //           }
  //         }
  //}
  //  return this;
};

