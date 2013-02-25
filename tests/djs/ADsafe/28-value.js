/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document  = /*: Ref(~lDocument) */ "#extern";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var String =  /*: (Top) -> Str */ "#extern";

var purge_event_handlers = /*: (node: Ref(~lNode)) -> Top */ "#extern";

var value = function (value) 
/*: {( and 
    (v:: (this: Ref(~lBunch), value: {(= (tag v) "string")}) -> Top)
    (v:: (this: Ref(~lBunch), value: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
)}*/
{
  reject_global(this);
  if (value === undefined) {
    error("default");     //PV: added this
  }
  var b /*: Ref(~lNodes) */   = this.___nodes___, 
      i /*: {Int|(>= v 0)} */ = 0, 
      node /*: Ref(~lNode) */ = null;

  var cond /*: Bool */ = true;

  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    //PV: added extra if check for lengths
    if (b.length === value.length) {

      cond = i < b.length; 
      /*: b (~lNodes, thwd lNodes) */ "#freeze";
      /*: ( &value: {(ite (= (tag v) "array") (v::Ref(~lPackedValues)) (Top v))}) -> sameType*/
      for (i = 0; cond; i += 1) {
        /*: b lNodes */ "#thaw";
        if (i < b.length) {
          node = b[i];
          /*: b (~lNodes, thwd lNodes) */ "#freeze";

          if (node.tagName) {
            if (node.type !== 'password') {
              if (typeof node.value === 'string') {
                /*: node lNode */ "#thaw";
                node.value = value[i];
                /*: node (~lNode, thwd lNode) */ "#freeze";
              } 
              else {
                /*: (&node: Ref(~lNode)) -> sameType */
                while (node.firstChild) {
                  purge_event_handlers(node.firstChild);
                  node.removeChild(node.firstChild);
                }
//                node.appendChild(document.createTextNode(String(value[i])));
              }
            }
          } else if (node.nodeName === '#text') {
//            node.nodeValue = String(value[i]);
          }
        }
        else {
          /*: b (~lNodes, thwd lNodes) */ "#freeze";
        }
      }
    }
    else {
      /*: b (~lNodes, thwd lNodes) */ "#freeze";
    }
  } 
  else {
//    value = String(value);
//    /*: b lNodes */ "#thaw";
//    b.l;
//    /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
//        -> ( &b: sameType, lNodes: sameType) */ 
//    for (i = 0; i < b.length; i += 1) {
//      node = b[i];
//      if (node.tagName) {
//        if (node.tagName !== 'BUTTON' &&
//            typeof node.value === 'string') {
//              node.value = value;
//            } else {
//              /*: (&node: Ref(~lNode)) -> sameType */
//              while (node.firstChild) {
//                purge_event_handlers(node.firstChild);
//                node.removeChild(node.firstChild);
//              }
//              node.appendChild(document.createTextNode(value));
//            }
//      } else if (node.nodeName === '#text') {
//        node.nodeValue = value;
//      }
//    }
//    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};
