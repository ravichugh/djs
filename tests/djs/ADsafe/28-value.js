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

var purge_event_handlers = /*: (node: Ref(~htmlElt)) -> Top */ "#extern";

var value = function (value) 
//TODO: intersection type
/* {( and 
    (v:: (this: Ref(~lBunch), value: {(= (tag v) "string")}) / (lValue: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType) 
    (v:: (this: Ref(~lBunch), value: Ref(lValue)) / (lValue: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType) 
)}*/
  
/* (this: Ref(~lBunch), value: Str) -> Top */
/*:  (this: Ref(~lBunch), value: Ref(lValue)) / (lValue: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType */
{
  reject_global(this);
  if (value === undefined) {
    error("default");     //PV: added this
  }
  var b /*: Ref(~htmlElts) */   = this.___nodes___, 
      i /*: {Int|(>= v 0)} */ = 0, 
      node /*: Ref(~htmlElt) */ = null;

  var cond /*: Bool */ = true;

  if (isArray(value)) {
    /*: b htmlElts */ "#thaw";
    //PV: added extra if check for lengths
    if (b.length === value.length) {

      cond = i < b.length; 
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

      /*: ( &value: Ref(lValue), lValue: {Arr(Str)|(packed v)} > lArrPro ) -> sameType*/
      for (i = 0; cond; i += 1) {
        /*: b htmlElts */ "#thaw";
        if (i < b.length) {
          node = b[i];
          /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

          if (node.tagName) {
            if (node.type !== 'password') {
              if (typeof node.value === 'string') {
                /*: node htmlElt */ "#thaw";
                node.value = value[i];
                /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
              } 
              else {
                /*: (&node: Ref(~htmlElt)) -> sameType */
                while (node.firstChild) {
                  purge_event_handlers(node.firstChild);
                  node.removeChild(node.firstChild);
                }
                node.appendChild(document.createTextNode(String(value[i])));
              }
            }
          } else if (node.nodeName === '#text') {
            node.nodeValue = String(value[i]);
          }
        }
        else {
          /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
        }
      }
    }
    else {
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    }
  } 
  else {
    value = String(value);
    /*: b htmlElts */ "#thaw";
    b.l;
    /*: ( &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
        -> ( &b: sameType, htmlElts: sameType) */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      if (node.tagName) {
        if (node.tagName !== 'BUTTON' &&
            typeof node.value === 'string') {
              node.value = value;
            } else {
              /*: (&node: Ref(~htmlElt)) -> sameType */
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
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  return this;
};
