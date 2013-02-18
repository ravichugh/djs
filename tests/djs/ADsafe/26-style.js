
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";


var reject_name = /*: (name: Str) -> Top */ "#extern";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

var int_to_string /*: (Int) -> Str */ = "#extern";

var style = function (name, value) 
/*: {( and 
    (v:: (this: Ref(~lBunch), name: Str, value: Str) -> Ref(~lBunch))
    (v:: (this: Ref(~lBunch), name: Str, value: Ref(lA)) 
    / (lA: {Arr(Str)|(packed v)} > lArrPro) -> Ref(~lBunch) / sameType)
)}*/
{
  reject_global(this);
  if (reject_name(name)) {
    error("ADsafe style violation.");
  }
//TODO: RegEx
//  if (value === undefined || /url/i.test(string_check(value))) {
//    error();
//  }
  var b = this.___nodes___,
      i /*: {Int|(>= v 0)}*/ = 0,
      node /*: Ref(~lNode) */ = null,
      v /*: Str */ = "";
  var style /*: Ref(~lStyle) */ = null;     //PV: added this
  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    if (value.length !== b.length) {
//TODO: proto links differ       
//      error("ADsafe: Array length: " +
//          int_to_string(b.length) + "-" + int_to_string(value.length)); //PV: conversion
    }
    /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro) 
         -> sameType */ 
    for (i = 0; i < b.length && i < value.length; i += 1) { //PV: added i < len(value)
      node = b[i];
      /*: node lNode */ "#thaw";
      v = string_check(value[i]);
//TODO: RegEx
//      if (/url/i.test(v)) {
//        error();
//      }
      if (node.tagName) {
//TODO: this will be hard to TC without knowing what v is         
//        style = node.style;
//        /*: style lStyle */ "#thaw";
//        if (name !== "float") {
//          style[name] = v;
//        } 
//        else {
//          style.cssFloat = style.styleFloat = v;
//        }
//        /*: style (~lStyle, thwd lStyle) */ "#freeze";
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  else {
    v = string_check(value);
//TODO: RegEx
//    if (/url/i.test(v)) {
//      error();
//    }
    /*: b lNodes */ "#thaw";
    b.l;
    /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro) 
         -> sameType */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
//TODO: same as above        
//        style = node.style;
//        /*: style lStyle */ "#thaw";
//        if (name !== "float") {
//          style[name] = v;
//        } else {
//          style.cssFloat = style.styleFloat = v;
//        }
//        /*: style (~lStyle, thwd lStyle) */ "#freeze";
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return this;
};
