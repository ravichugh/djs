/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyBunchObj { "___nodes___": Ref(~lNodes), "___star___": Bool} > lObjPro */ "#define";
/*: tyBunchArr { Arr(Ref(~lBunch))|(packed v)} > lArrPro */ "#define";

var star    /*: Bool */ = "#extern";
var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var purge_event_handlers = /*: (node: Ref(~lNode)) -> Top */ "#extern";


var array_check  = function(a) /*: [;L;] (a: Ref(L)) / (L: tyBunchArr) -> Top / sameExact */ {};

var object_check = function(a) /*: [;L;] (a: Ref(L)) / (L: tyBunchObj) -> Top / sameExact */ {};


var replace = function (replacement)
/*: {(and
        (v:: (this: Ref(~lBunch), replacement: Ref(lA)) / (lA: tyBunchArr) -> Top / sameExact )
        (v:: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact )
    )} */
{
  reject_global(this);
  var b = this.___nodes___,
      flag = false,
      i /*: { Int | (>= v 0)} */ = 0,
      j /*: { Int | (>= v 0)} */ = 0,
      newnode /*: Ref(~lNode) */ = null,
      node /*: Ref(~lNode) */ = null,
      parent /*: Ref(~lNode) */ = null,
      rep /*: Ref(~lNodes) */ = null;
  
  var cond;   //PV: added this
  
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


  if (    !replacement 
      ||  replacement.length === 0 
      ||  (replacement.___nodes___ /*&& replacement.___nodes___.length === 0*/) //TODO
    )
  {
    /*: b lNodes */ "#thaw";
    /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> sameType */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      purge_event_handlers(node);
      if (node.parentNode) {
        node.parentNode.removeChild(node);
      }
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  else if (isArray(replacement)) {
    /*: b lNodes */ "#thaw";
    if (replacement.length !== b.length) {
      //error('ADsafe: Array length: ' +
      //    b.length + '-' + value.length);
    }

//    //PV: added extra condition - might be able to infer this
    cond = i < b.length && i < replacement.length;
    /*: b (~lNodes, thwd lNodes) */ "#freeze";

    /*: (&b: Ref(~lNodes), &cond: Bool) -> sameType */ 
    for (i = 0; cond; i += 1) {
      /*: b lNodes */ "#thaw";
      cond = i < b.length && i < replacement.length;
      if (cond) {
        node = b[i];
//        parent = node.parentNode;
        purge_event_handlers(node);
      }
      /*: b (~lNodes, thwd lNodes) */ "#freeze";
//TODO: 
      if (parent) {
        if (i < replacement.length) {
//          rep = replacement[i].___nodes___;
//          assert(/*: Ref(~lNodes) */ (rep));
//          /*: rep lNodesRep */ "#thaw";
//          rep.length;
//          if (rep.length > 0) {
//            newnode = rep[0];
//            parent.replaceChild(newnode, node);
//            /*: (&rep: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro) -> sameType */ 
//            for (j = 1; j < rep.length; j += 1) {
//              node = newnode;
//              newnode = rep[j];
//              parent.insertBefore(newnode, node.nextSibling);
//            }
//          }
//          /*: rep (~lNodes, thwd lNodesRep) */ "#freeze";
        } else {
//          parent.removeChild(node);
        }
      }
    }
  } 
  else {
//    rep = replacement.___nodes___;
//    for (i = 0; i < b.length; i += 1) {
//      node = b[i];
//      purge_event_handlers(node);
//      parent = node.parentNode;
//      if (parent) {
//        newnode = flag ? rep[0].cloneNode(true) : rep[0];
//        parent.replaceChild(newnode, node);
//        for (j = 1; j < rep.length; j += 1) {
//          node = newnode;
//          newnode = flag ? rep[j].clone(true) : rep[j];
//          parent.insertBefore(newnode, node.nextSibling);
//        }
//        flag = true;
//      }
//    }
  }

  return this;
};

