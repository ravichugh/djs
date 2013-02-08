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
    (v:: (this: Ref(~lBunch), value: Str)     / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
    (v:: (this: Ref(~lBunch), value: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
)}*/
{
  reject_global(this);
  if (value === undefined) {
    error("default");     //PV: added this
  }
  var b = this.___nodes___, i /*: {Int|(>= v 0)} */ = 0, node /*: Ref(~lNode) */ = null;
  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    b.l;
//TODO: not working with length check !!!
//    if (b.length === value.length) {  //PV: added extra if clause for lengths
      /*: ( &value: Ref(lT), lT:{Arr(Str)|(packed v)} > lArrPro,
            &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
          -> ( &value: sameType, lT: sameType, &b: sameType, lNodes: sameType) */ 
      for (i = 0; i < b.length && i < value.length; i += 1) {
        node = b[i];
        if (node.tagName) {
          if (node.type !== 'password') {
            if (typeof node.value === 'string') {
              node.value = value[i];
            } else {
              /*: (&node: Ref(~lNode)) -> sameType */
              while (node.firstChild) {
                purge_event_handlers(node.firstChild);
                node.removeChild(node.firstChild);
              }
              node.appendChild(document.createTextNode(
                    String(value[i])
                    ));
            }
          }
        } else if (node.nodeName === '#text') {
          node.nodeValue = String(value[i]);
        }
      }
//    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  } 
  else {
    value = String(value);
    /*: b lNodes */ "#thaw";
    b.l;
    /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
        -> ( &b: sameType, lNodes: sameType) */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      if (node.tagName) {
        if (node.tagName !== 'BUTTON' &&
            typeof node.value === 'string') {
              node.value = value;
            } else {
              /*: (&node: Ref(~lNode)) -> sameType */
              while (node.firstChild) {
                purge_event_handlers(node.firstChild);
                node.removeChild(node.firstChild);
              }
              node.appendChild(document.createTextNode(value));
            }
      } else if (node.nodeName === '#text') {
        node.nodeValue = value;
      }
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};
