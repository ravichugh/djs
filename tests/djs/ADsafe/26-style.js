
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
/* {( and 
    (v:: (this: Ref(~lBunch), name: Str, value: Str) -> Ref(~lBunch))
    (v:: (this: Ref(~lBunch), name: Str, value: Ref(lA)) 
    / (lA: {Arr(Str)|(packed v)} > lArrPro) -> Ref(~lBunch) / sameType)
)}*/

//TODO: both work for the right part of the code but not the intersection type
/*: (this: Ref(~lBunch), name: Str, value: Str) -> Ref(~lBunch) */
/* (this: Ref(~lBunch), name: Str, value: Ref)
    / (value: {Arr(Str)|(packed v)} > lArrPro) -> Ref(~lBunch) / sameType */
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
      node /*: Ref(~htmlElt) */ = null,
      v /*: Str */ = "";
  
  var style /*: Ref(~lStyle) */ = null;     //PV: added this

  var tmp_bl;

  if (isArray(value)) {
//    /*: b htmlElts */ "#thaw";
//    if (value.length !== b.length) {
//      tmp_bl = b.length;
//      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//      error("ADsafe: Array length: " + int_to_string(tmp_bl)
//        + "-" + int_to_string(value.length)); //PV: conversion
//    }
//    else {
//      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//    }
//    /*: b htmlElts */ "#thaw";
//
//    /*: ( &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) 
//         -> sameType */ 
//    for (i = 0; i < b.length && i < value.length; i += 1) { //PV: added i < len(value)
//      node = b[i];
//      /*: node htmlElt */ "#thaw";
//      v = string_check(value[i]);
//////TODO: RegEx
//////      if (/url/i.test(v)) {
//////        error();
//////      }
//      if (node.tagName) {
//        style = node.style;
//        /*: style lStyle */ "#thaw";
//        if (name !== "float") {
//          style[name] = v;
//        } 
//        else {
//          style.cssFloat = style.styleFloat = v;
//        }
//        /*: style (~lStyle, thwd lStyle) */ "#freeze";
//      }
//      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
//    }
//    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  else {
    v = string_check(value);
//TODO: RegEx
//    if (/url/i.test(v)) {
//      error();
//    }
    /*: b htmlElts */ "#thaw";
    assume(b != null);
    /*: ( &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) 
         -> sameType */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      assume(node != null);
      if (node.tagName) {
        style = node.style;
        /*: style lStyle */ "#thaw";
        if (name !== "float") {
          style[name] = v;
        } else {
          style.cssFloat = style.styleFloat = v;
        }
        /*: style (~lStyle, thwd lStyle) */ "#freeze";
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  return this;
};
