// addon-sdk/lib/sdk/lang/type.js



/* vim:ts=2:sts=2:sw=2:
 * ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is Jetpack.
 *
 * The Initial Developer of the Original Code is Mozilla.
 * Portions created by the Initial Developer are Copyright (C) 2010
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Irakli Gozalishvili <gozala@mozilla.com> (Original Author)
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */

/*****************************************************
 *
 *
 * Information flow properties
 *
 *
 *****************************************************/

//For every dictionary d:
//  All fields in d are public ==> d is public

/*: (forall (d) 
      (implies 
        (forall (f) (and (has d f) (public (sel d f))))
        (public d)
      )
    ) */ "#assume";


/// If a dictionary contains a privilieged binding then it's privileged itself
/*: (forall (d f)
        (implies (and (has d f) (isPrivileged (sel d f))) (isPrivileged d))
    ) */ "#assume";

//// All fields of a privileged dictionary are privileged
///*: (forall (d f)
//      (implies 
//        (isPrivileged d)
//        (implies (has d f) (isPrivileged (sel d f)))
//      )
//    ) */ "#assume";


// Public values:
/*: (public undefined)   */ "#assume";
/*: (public true)        */ "#assume";
/*: (public null)        */ "#assume";
/*: (public "string")    */ "#assume";
/*: (public "undefined") */ "#assume";
/*: (public "boolean")   */ "#assume";
/*: (public "number")    */ "#assume";
/*: (public "null")      */ "#assume";
/*: (public "function")  */ "#assume";
/*: (public "array")     */ "#assume";
/*: (public "object")    */ "#assume";

/*: (public "dummy")     */ "#assume";
/*: (public "")          */ "#assume";
/*: (public "#")         */ "#assume";
/*: (public "qq")        */ "#assume";
/*: (public ",n")        */ "#assume";
/*: (public "n")         */ "#assume";
/*: (public ": ")        */ "#assume";

/*: (public 1)           */ "#assume";


//DJS cannot use: 
// /*: (public ",\n")         */ "#assume";


/*****************************************************
 *
 *
 * DJS definitions
 *
 *
 *****************************************************/

/*: "tests/djs/sif/__mozilla.dref" */ "#use";

/*: allFrozenLocations 
 ~obj: frzn, ~pubObj: frzn, ~strArr: frzn, ~pstrArr: frzn, ~pubArr: frzn,
 ~descriptor: frzn, ~extern: frzn, ~lFlashblock: frzn, ~lRegExp: frzn,
 ~lInput: frzn, ~lTab: frzn, ~lBrowser: frzn, ~nsIScriptableInputStream: frzn,
 ~nsIFileOutputStream: frzn, ~nsIFileInputStream: frzn, ~nsIProperties: frzn,
 ~nsIFile: frzn, ~nsIFilePicker: frzn, ~nsIFilePicker: frzn, ~lWindow: frzn,
 ~lConsole: frzn, ~lComponents: frzn, ~lComponents_interfaces: frzn,
 ~lComponents_classes: frzn, ~nsIExtensionManager: frzn, ~lnsIUpdateItem:
 frzn, ~lMOPService: frzn, ~nsIPrefService: frzn, ~nsIPrefBranch: frzn,
 ~lMFilePicker: frzn, ~lMEManager: frzn, ~lMFApplication: frzn,
 ~lMScriptableInputStream: frzn, ~lMNFileOutputStream: frzn,
 ~lMNFileInputStream: frzn, ~lMFileLocal: frzn, ~lMFDirService: frzn,
 ~dirLocator: frzn, ~fuelIApplication: frzn, ~lApplication_extensions: frzn,
 ~lExtensions: frzn, ~lPreferences: frzn, ~topArr: frzn
*/ "#define";

/*: PStr {Str |(public v)} */ "#define";
/*: PBool {Bool |(public v)} */ "#define";
/*: PInt {Int |(public v)} */ "#define";
/*: NonNegInt {Int |(>= v 0)} */ "#define";
/*: Pub {(public v)} */ "#define";

/*: tyPubArr Arr(Pub) */ "#define";
/*: (~pubArr: tyPubArr > lArrPro) */ "#weak";
/*: (~pstrArr: Arr(PStr) > lArrPro) */ "#weak";

/*: (~strArr: Arr(Str) > lArrPro) */ "#weak";

/*: (~pubObj: {Dict|(public v)} > lObjPro) */ "#weak";

/*: (~obj: { } > lObjPro) */ "#weak";

/*: (~topArr: Arr(Top) > lArrPro) */ "#weak";

/*: tyDescriptor {
    configurable: Bool,
    enumerable: Bool,
    writable: Bool,
    value: Ref(~pubObj),
    get: () -> Top,
    set: (Top) -> Top
  } > lObjPro */ "#define";


var exports = /*: Ref(~extern) */ "#extern";

var objectGetPrototypeOf = 
/*: (o:Ref) / (o: Top > o.pro) -> Ref(o.pro) / (o: sameExact) */
"#extern";

var String = /*: (Top) -> Str */ "#extern";

var arrayIndexOf = 
/*: (a:Ref, e:Top) / (a: Top > a.pro) 
      -> {Int|(>= v (- 0 1))} / (a: sameExact) */ "#extern";

var intToString = /*: (Int) -> PStr */ "#extern";

var boolToString = /*: ({Bool|(public v)}) -> PStr */ "#extern";

var objToString = 
/*: (o:Ref) / (o: Top > o.pro) -> Str / (o:sameExact) */ "#extern";

//PV: Should return a new location like the first commented version but gets
//complicated later, when the `value` referes to two prossible locations. 
var arraySlice =
  /* [A;La,Lr] (Ref(La), Int, Int) / (La: Arr(A) > lArrPro) 
      -> Ref(Lr) / (La: sameExact, Lr: Arr(A) > lArrPro) */
  /*: [A;La,Lapro,Lr] (Ref(La), Int, Int) / (La: Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: Arr(A) > Lapro) */
  /* [A;La] (Ref(La), Int, Int) / (La: Arr(A) > lArrPro) 
      -> Ref(La) / (La: sameExact) */ "#extern";

var arrayMap = 
/*: [A,B; La, Lapro, Lr] (Ref(La), (A) / (allFrozenLocations) -> B / sameExact) 
      / (La: Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: Arr(B) > lArrPro) */ "#extern";

var arrayJoin = 
/*: [A;L] (Ref(L), Str) / (L: Arr(A) > lArrPro) -> Str / (L:sameExact) */ "#extern";

var arrayEvery = 
/*: [A;L] (Ref(L), (Top) / (allFrozenLocations) -> Bool / sameType) 
      / (L: Arr(A) > lArrPro) -> Bool / sameType */ "#extern";

var objectKeys = 
/*: [;L,L1,Lr] (Ref(L)) / (L:Top > L1) 
      -> Ref(Lr) / (L:sameExact, Lr: Arr(Str) > lArrPro) */ 

/* (o:Ref) / (o: Dict > lObjPro) -> Ref(lArr) / (lArr: Arr(Str) > lArrPro) */
/* [;L;] (a:Ref) / (a: Arr(NotUndef) > lArrPro) 
    -> Ref(L) / (L: Arr(Str) > lArrPro, a: sameExact) */ 
/* [;L] (Top) / () -> Ref(L) / (L: Arr(Str) > lArrPro) */
"#extern";

var objectGetOwnPropertyDescriptor = 
/* [;Ld,Lo] (Ref(Lo)) / (Lo: { } > lObjPro) 
        -> Ref(~descriptor) / (Lo: sameExact)) */
/* (Top) -> Ref(~descriptor) */

/*: [;L,Lp,Ld] (a:Ref(L)) / (L: Top > Lp) 
        -> Ref(Ld) / (L: sameExact, Ld: tyDescriptor) */
"#extern";

var norToBool = /*: (Int) -> Bool */ "#extern";

var randomBool = /*: () -> Bool */ "#extern";

var toString = /*: (Top) -> Str */ "#extern";

var stringSplit = 
/*: [;L] (Str, Str) / () -> Ref(L) / (L: Arr(Str) > lArrPro) */ "#extern";

var arraySplice = 
/*: [A;L,Lr] (Ref(L), Int, Int) / (L: Arr(A) > lArrPro) 
      -> Ref(Lr) / (L:sameExact, Lr: Arr(A) > lArrPro) */ "#extern";


/*****************************************************
 *
 *
 * Module code starts here
 *
 *
 *****************************************************/

"use strict";

/**
 * Returns `true` if `value` is `undefined`.
 * @examples
 *    var foo; isUndefined(foo); // true
 *    isUndefined(0); // false
 */
//TODO: changed this cause the arrays would not TC
var isUndefined = function(value) 
/* (Pub) -> {Bool|(public v)} */ 
/*: (Top) -> Bool */ 
{
  return value === undefined;
};
exports.isUndefined = isUndefined;


/**
 * Returns `true` if value is `null`.
 * @examples
 *    isNull(null); // true
 *    isNull(undefined); // false
 */
var isNull = function(value) 
/* ({(public v)}) -> {Bool|(public v)} */ 
/*: (Top) -> Bool */ 
{
  return value === null;
};
exports.isNull = isNull;

/**
 * Returns `true` if value is a string.
 * @examples
 *    isString("moe"); // true
 */
var isString = function(value) 
/*: (value: Top) -> {Bool|(and (iff (= v true) (Str value)) (implies (public value) (public v)))} */ 
{
  return typeof value === "string";
};
exports.isString = isString;

/**
 * Returns `true` if `value` is a number.
 * @examples
 *    isNumber(8.4 * 5); // true
 */
var isNumber = function(value) 
/*: (value: {(public v)}) -> {Bool|(and (iff (= v true) (Num value)) (public v))} */ 
{
  return typeof value === "number";
};
exports.isNumber = isNumber;

//TODO
//Does instanceof work?
///**
// * Returns `true` if `value` is a `RegExp`.
// * @examples
// *    isRegExp(/moe/); // true
// */
//function isRegExp(value) {
//  return isObject(value) && instanceOf(value, RegExp);
//}
//exports.isRegExp = isRegExp;

///**
// * Returns true if `value` is a `Date`.
// * @examples
// *    isDate(new Date()); // true
// */
//var isDate = function(value) 
//
//{
//  return isObject(value) && instanceOf(value, Date);
//}
//exports.isDate = isDate;

/**
 * Returns true if object is a Function.
 * @examples
 *    isFunction(function foo(){}) // true
 */
var isFunction = function(value) 
/* (value: Top) -> {Bool|(and (iff (= v true) (= (tag value) "function")) (implies (public value) (public v)))} */
/* (value: Top) -> {Bool|(implies (public value) (public v))} */
/*: (value: Top) -> {Bool|(iff (= v true) (and (= (tag value) "function") (not (= (tag value) "object"))   (not (= (tag value) "array")) ))} */
{
    return typeof value === "function";
};
exports.isFunction = isFunction;

/**
 * Returns `true` if `value` is an object (please note that `null` is considered
 * to be an atom and not an object).
 * @examples
 *    isObject({}) // true
 *    isObject(null) // false
 */
var isObject = function(value) 
/* (value: {(public v)}) -> {Bool|(and (iff (= v true) (and (not (= value null)) (= (tag value) "object"))) (public v))} */
/* (value: Top) -> {Bool|(and (iff (= v true) (and (not (= value null)) (= (tag value) "object"))))} */
/*: (value: Top) -> {Bool|(implies (public value) (public v))} */
{ 
    return typeof value === "object" && value !== null;
};
exports.isObject = isObject;

//TODO
///**
// * Returns true if `value` is an Array.
// * @examples
// *    isArray([1, 2, 3])  // true
// *    isArray({ 0: 'foo', length: 1 }) // false
// */
//var isArray = Array.isArray || function isArray(value) {
//  Object.prototype.toString.call(value) === "[object Array]";
//}
//exports.isArray = isArray;

///**
// * Returns `true` if `value` is an Arguments object.
// * @examples
// *    (function(){ return isArguments(arguments); })(1, 2, 3); // true
// *    isArguments([1,2,3]); // false
// */
//function isArguments(value) {
//  Object.prototype.toString.call(value) === "[object Arguments]";
//}
//exports.isArguments = isArguments;

/**
 * Returns true if it is a primitive `value`. (null, undefined, number,
 * boolean, string)
 * @examples
 *    isPrimitive(3) // true
 *    isPrimitive('foo') // true
 *    isPrimitive({ bar: 3 }) // false
 */
var isPrimitive = function(value) 
/*: (value: Top) -> {Bool|(implies (public value) (public v))} */
{
  return !isFunction(value) && !isObject(value);
};
exports.isPrimitive = isPrimitive;

/**
 * Returns `true` if given `object` is flat (it is direct decedent of
 * `Object.prototype` or `null`).
 * @examples
 *    isFlat({}) // true
 *    isFlat(new Type()) // false
 */
var isFlat = function(object) 
/*:  [;L1,L2,L3] (Ref(L1)) / (L1: Top > L2, L2 : Top > L3) -> Bool / (L1: sameExact) */
{
  //PV: Original code begin
  //return isObject(object) && (isNull(Object.getPrototypeOf(object)) ||
  //                            isNull(Object.getPrototypeOf(
  //                                   Object.getPrototypeOf(object))));
  //PV: Original code end

  var t0 = (/*: [;L1,L2] */ objectGetPrototypeOf)(object);
  var t1 = (/*: [;L2,L3] */ objectGetPrototypeOf)(t0);
  return isObject(object) && (isNull(t0) || isNull(t1));
};

exports.isFlat = isFlat;



/**
 * Returns `true` if object contains no values.
 */
var isEmpty = function(object)
/*: (object: { Ref(lObj) | (public v)}) / 
    (lObj: Dict > lObjPro) -> Bool / sameType */
{
  //PV: Original code begin
  //if (isObject(object)) {
  //  for (var key in object)
  //    return false;
  //  return true;
  //}
  //return false;
  //PV: Original code end

  if (isObject(object)) {
    var key /*: Str */ = "";
    var cnt /*: Bool */ = true;
    /*: ( lObj: Dict > lObjPro) -> sameType */
    for (key in object)
      cnt = false;
    return cnt;

  }
  return false;
};
exports.isEmpty = isEmpty;




/*: isJSON :: 
  (value: Ref(l1), visited: Ref(l2)) / (l1: Arr(NotUndef) > lArrPro, l2: Arr(Top) > lArrPro)
        -> {Bool|(implies (public value) (public v))} / sameType */ "#type";


/**
 * Returns `true` if `value` is an array / flat object containing only atomic
 * values and other flat objects.
 */
var isJSON = function(value, visited) {

//    // Adding value to array of visited values.
//    //PV: Original code begin
//    //(visited || (visited = [])).push(value);
//    //PV: Original code end
//
//    //XXX: TODO + SLOW DOWN !!!
//    if (!visited) {
//      visited = /*: lEmpty Arr(Top) */ [value];
//    }
//    else {
//      visited.push(value);
//    }
  
    //PV: Original code begin
    //        // If `value` is an atom return `true` cause it's valid JSON.
    //return  isPrimitive(value) ||
    //        // If `value` is an array of JSON values that has not been visited
    //        // yet.
    //        (isArray(value) &&  value.every(function(element) {
    //                              return isJSON(element, visited);
    //                            })) ||
    //        // If `value` is a plain object containing properties with a JSON
    //        // values it's a valid JSON.
    //        (isFlat(value) && Object.keys(value).every(function(key) {
    //            var $ = Object.getOwnPropertyDescriptor(value, key);
    //            // Check every proprety of a plain object to verify that
    //            // it's neither getter nor setter, but a JSON value, that
    //            // has not been visited yet.
    //            return  ((!isObject($.value) || !~visited.indexOf($.value)) &&
    //                    !('get' in $) && !('set' in $) &&
    //                    isJSON($.value, visited));
    //        }));
    //PV: Original code end


    var f1 = function(element) /*: (Top) -> Bool */ {
      //TODO
      //return isJSON_(element, visited);
      return true;
    }; 

    var f2 = function(key) /*: (Str) -> Bool */ {
      var $ = /*: [;l1,lArrPro,ld] */ objectGetOwnPropertyDescriptor(value, key);
      // Check every proprety of a plain object to verify that
      // it's neither getter nor setter, but a JSON value, that
      // has not been visited yet.
      return  ((!isObject($.value) || norToBool(arrayIndexOf(visited,$.value)))
          //TODO
          //&& !('get' in $) && !('set' in $) && isJSON_($.value, visited)
          );
    };


    var keys = /*: [;l1,lArrPro,lk1] */ objectKeys(value);

    // If `value` is an atom return `true` cause it's valid JSON.
    var result = 
      isPrimitive(value) 
         // If `value` is an array of JSON values that has not been visited
         // yet.
    ||  ( isArray(value) && arrayEvery(value, f1) )
         // If `value` is a plain object containing properties with a JSON
         // values it's a valid JSON.
    //TODO
    //||  ( /*: [;l1,lArrPro,lROOT] */ isFlat(value) && (/*: [Str;lk1] */ arrayEvery)(keys,f2) ) 
    ;
    
    return result;
};

//exports.isJSON = function (value) {
//  return isJSON(value);
//};


//TODO
///**
// * Returns if `value` is an instance of a given `Type`. This is exactly same as
// * `value instanceof Type` with a difference that `Type` can be from a scope
// * that has a different top level object. (Like in case where `Type` is a
// * function from different iframe / jetpack module / sandbox).
// */
//function instanceOf(value, Type) {
//  var isConstructorNameSame;
//  var isConstructorSourceSame;
//
//  // If `instanceof` returned `true` we know result right away.
//  var isInstanceOf = value instanceof Type;
//
//  // If `instanceof` returned `false` we do ducktype check since `Type` may be
//  // from a different sandbox. If a constructor of the `value` or a constructor
//  // of the value's prototype has same name and source we assume that it's an
//  // instance of the Type.
//  if (!isInstanceOf && value) {
//    isConstructorNameSame = value.constructor.name === Type.name;
//    isConstructorSourceSame = String(value.constructor) == String(Type);
//    isInstanceOf = (isConstructorNameSame && isConstructorSourceSame) ||
//                    instanceOf(Object.getPrototypeOf(value), Type);
//  }
//  return isInstanceOf;
//}
//exports.instanceOf = instanceOf;



/**
 * Function returns textual representation of a value passed to it. Function
 * takes additional `indent` argument that is used for indentation. Also
 * optional `limit` argument may be passed to limit amount of detail returned.
 * @param {Object} value
 * @param {String} [indent="    "]
 * @param {Number} [limit]
 */
var source = function source_(value, indent, limit, offset, visited) 
//BOTH WORK!!!
/*: [;Lv,L1,Lvis0] (value:Ref(Lv), Str, Int, Str, Ref(Lvis0))
    / (Lv: Arr(Top) > L1, Lvis0: Arr(Top) > lArrPro) -> Top / (Lv: sameType) */

/* [;Lv,L1,Lvis0] (value:Ref(Lv), PStr, PInt, PStr, visited: Ref(Lvis0)) 
    / (Lv: {      } > L1, Lvis0: Arr(Top) > lArrPro) -> Top / (Lv: sameType) */
{

  var result;
  var names;
  var nestingIndex;
  var isCompact = !isUndefined(limit);

  indent = indent || "    ";
  offset = (offset || "");
  result = "";

  //PV: Original code begin
  //visited = visited || /*: lArr Arr(Top) */ [];
  //PV: Original code end

  if (visited) {
    /*: visited (~topArr, frzn) */ "#freeze";    
  }
  else {
    visited = /*: lArr Arr(Top) */ []; 
    /*: visited (~topArr, frzn) */ "#freeze";    
  }

  if (isUndefined(value)) {
    result += "undefined";
  }
  else if (isNull(value)) {
    result += "null";
  }
  else if (isString(value)) {
    //PV: Original code begin
    //result += '"' + value + '"';
    //PV: Original code end

    result += "qq" + value + "qq";
  }
  else if (isFunction(value)) {
    //PV: Original code begin
    //value = String(value).split("\n");
    //PV: Original code end

    var tmp0 = /*: [;lvs] */ stringSplit(toString(value), "\n");
    if (isCompact && tmp0.length > 2) {
      //PV: Original code begin
      //value = value.splice(0, 2);
      //PV: Original code end

      tmp0 = /*: [Str;lvs,lvs1] */ arraySplice(tmp0, 0, 2);
      //XXX: SLOW DOWN !!! + 17 sec
      //tmp0.push("...}");
      /*: tmp0 (~strArr, frzn) */ "#freeze";
      value = tmp0;
    }
    else {
      /*: tmp0 (~strArr, frzn) */ "#freeze";
      value = tmp0;
    }

    //PV: Original code begin
    //result += value.join("\n" + offset);
    //PV: Original code end
    
    /*: value lval0 */ "#thaw";
    result += /*: [Str; lval0] */ arrayJoin(value, "\n" + offset);
    /*: value (~strArr, thwd lval0) */ "#freeze";
    result += ("a\nb" + offset);
  }
  else if (isArray(value)) {
    //PV: original code begin
    //if ((nestingIndex = (visited.indexOf(value) + 1))) {
    //  result = "#" + nestingIndex + "#";
    //}
    //PV: original code end

    /*: visited lvis */ "#thaw";
    nestingIndex = arrayIndexOf(visited, value) + 1;
    /*: visited (~topArr, thwd lvis) */ "#freeze";    

    if (nestingIndex) {
      result = "#" + intToString(nestingIndex) + "#";
    }
    else {
      //XXX: SLOW DOWN !!! + 25 sec
      ///*: visited lvis */ "#thaw";
      //visited.push(value);
      ///*: visited (~topArr, thwd lvis) */ "#freeze";    

      //PV: original code begin
      //if (isCompact)
      //  value = /*: [Top; Lv,L1,lsl1] */ arraySlice(value, 0, limit);
      //PV: original code end
      

      var tmp2;
      /*: (~locTopArr: Arr(Top) > L1) */ "#weak";

      if(isCompact) {
        tmp2 = /*: [Top;Lv,L1,lsl1] */ arraySlice(value, 0, limit);
        /*: value (~locTopArr, frzn) */ "#freeze";    
        /*: tmp2 (~locTopArr, frzn) */ "#freeze"; 
      }
      else {
        /*: value (~locTopArr, frzn) */ "#freeze";    
        tmp2 = value;
      }
      
      /*: value Lv */ "#thaw";

      //PV: Original code
      //result += "[\n";
      //result += value.map(function(value) {
      //  return offset + indent + 
      //    source_(value, indent, limit, offset + indent, visited);
      //}).join(",\n");
      //PV: orignial code end

      result += "n";
      var f1 = function(value_) /*: (Top) -> Str */ {
        //TODO
        return offset + indent /*+ source_(value, indent, limit, offset + indent, visited)*/;
      };
      var tmp1 = /*: [Top,Str; Lv,L1,lm] */ arrayMap(value, f1); 

      //PV: orignial code begin
      //result += arrayJoin(tmp1, ",\n");
      //result += isCompact && value.length > limit ?
      //          ",\n" + offset + "...]" : "\n" + offset + "]";
      //PV: orignial code end
      
      result += /*: [Str;lm] */ arrayJoin(tmp1, ",n");
      result += (isCompact && value.length > limit) ? "dummy" : "dummy";

    }

  }
  else if (isObject(value)) {
    //PV: Original code begin
    //nestingIndex = (visited.indexOf(value) + 1);
    //PV: Original code end

    /*: visited lvis */ "#thaw";
    nestingIndex = arrayIndexOf(visited, value) + 1;
    /*: visited (~topArr, thwd lvis) */ "#freeze";    

    if (nestingIndex) {
      result = "#" + intToString(nestingIndex) + "#";
    }
    else {
      //XXX: SLOW DOWN !!!
      ///*: visited lvis */ "#thaw";
      //visited.push(value);
      ///*: visited (~topArr, thwd lvis) */ "#freeze";    

      //PV: Original code begin
      //names = Object.keys(value);
      //PV: Original code end

      names = /*: [;Lv,L1,lnames] */ objectKeys(value);
     
      //PV: Original code begin (Implicit coersion)
      //result += "{ // " + value + "\n";
      //PV: Original code end
      result += objToString(value);
      
      //PV: Original code begin
      //result += (isCompact ? names.slice(0, limit) : names).map(function(name) {
      //PV: Original code end
      
      var tmp3;
      if(isCompact) {
        tmp3 = /*: [Str;lnames,lArrPro,lsl2] */ arraySlice(names, 0, limit);
        /*: names (~strArr, frzn) */ "#freeze";    
        /*: tmp3 (~strArr, frzn) */ "#freeze"; 
      }
      else {
        /*: names (~strArr, frzn) */ "#freeze";    
        tmp3 = names;
      }     
      

      var f2 = function(name_) /*: (PStr) -> Str */ 
      {
        var _limit = isCompact ? limit - 1 : limit;
        var descriptor = /*: [;Lv,L1,ld] */ objectGetOwnPropertyDescriptor(value, name_);
        //PV: Original code begin
        //var result = offset + indent + "// ";
        //PV: Original code end
        
        var result_ = offset + indent;

        var accessor = "";
        if (0 <= name_.indexOf(" "))
          name_ = '"' + name_ + '"';

        if (descriptor.writable)
          result_ += "writable ";
        if (descriptor.configurable)
          result_ += "configurable ";
        if (descriptor.enumerable)
          result_ += "enumerable ";

        result_ += "\n";
        
        //PV: original code begin
        //XXX: TODO: SLOW DOWN
        //if ("value" in descriptor) {
        //PV: original code end

        if (randomBool()) {
          result_ += offset + indent + name_ + ": ";
          //TODO
          //result += source_(descriptor.value, indent, _limit, indent + offset, visited);
        }
        else {
          if (descriptor.get) {
            result_ += offset + indent + "get " + name_ + " ";
            //TODO
            //accessor = source_(descriptor.get, indent, _limit, indent + offset,
            //                  visited);
            result_ += accessor.substr(accessor.indexOf("{"));
          }

          if (descriptor.set) {
            result_ += offset + indent + "set " + name_ + " ";
            //TODO
            //accessor = source_(descriptor.set, indent, _limit, indent + offset,
            //                  visited);
            result_ += accessor.substr(accessor.indexOf("{"));
          }
        }
        

        return result_;
      };

      //PV: Original code begin
      //result += tmp3.map(f2).join(",\n");
      //PV: Original code end
      
      //PV: the definition of tmp4 needs to be here (before the thawing)
      var tmp4;
      /*: tmp3 ltmp3 */ "#thaw";
      tmp4 = /*: [Str,Str; ltmp3,lArrPro, lr] */ arrayMap(tmp3,f2);
      result += arrayJoin(tmp4, ",n");
      /*: tmp3 (~strArr, thwd ltmp3) */ "#freeze";    
      

      if (isCompact) {
        /*: names lnewnames */ "#thaw";
        if (names.length > limit && limit > 0) {
          result += ",\n" + offset  + indent + "//...";
        }
        /*: names (~strArr, thwd lnewnames) */ "#freeze";
      }
      else {
        /*: names lnewnames */ "#thaw";
        if (names.length)
          result += ",";
        /*: names (~strArr, thwd lnewnames) */ "#freeze";

        result += "\n" + offset + indent + '"__proto__": ';
        
        //PV: Original code begin
        //result += source(Object.getPrototypeOf(value), indent, 0,
        //                   offset + indent);
        //PV: Original code end
        
        var tmp5 = /*: [;Lv, L1] */ objectGetPrototypeOf(value);
        //TODO
        //result +=  /*: [;L1,lObjPro,lvis] */ source_(tmp5, indent, 0, offset + indent, visited);
      }
      result += "\n" + offset + "}";
    }
  } 
  else {
    //PV: Original code begin
    //result += String(value);  
    //PV: Original code end
    
    result += toString(value);
  }

  return result;

};

//exports.source = function (value, indentation, limit) {
//  return source(value, indentation, limit);
//};
