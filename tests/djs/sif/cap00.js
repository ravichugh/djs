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
/*: (public 1)           */ "#assume";


/*****************************************************
 *
 *
 * DJS definitions
 *
 *
 *****************************************************/

/*: "tests/djs/sif/__mozilla.dref" */ "#use";

/*: allFrozenLocations 
    ~extern: frzn, ~lFlashblock: frzn, ~lRegExp: frzn, ~lInput: frzn, ~lTab:
    frzn, ~lBrowser: frzn, ~nsIScriptableInputStream: frzn, ~nsIFileOutputStream:
    frzn, ~nsIFileInputStream: frzn, ~nsIProperties: frzn, ~nsIFile: frzn,
    ~nsIFilePicker: frzn, ~nsIFilePicker: frzn, ~lWindow: frzn, ~lConsole: frzn,
    ~lComponents: frzn, ~lComponents_interfaces: frzn, ~lComponents_classes:
    frzn, ~nsIExtensionManager: frzn, ~lnsIUpdateItem: frzn, ~lMOPService: frzn,
    ~nsIPrefService: frzn, ~nsIPrefBranch: frzn, ~lMFilePicker: frzn,
    ~lMEManager: frzn, ~lMFApplication: frzn, ~lMScriptableInputStream: frzn,
    ~lMNFileOutputStream: frzn, ~lMNFileInputStream: frzn, ~lMFileLocal: frzn,
    ~lMFDirService: frzn, ~dirLocator: frzn, ~fuelIApplication: frzn,
    ~lApplication_extensions: frzn, ~lExtensions: frzn, ~lPreferences: frzn */ "#define";

/*: PStr {Str |(public v)} */ "#define";
/*: Pub {(public v)} */ "#define";

/*: (~pubArr: {Arr(Pub)|(packed v)} > lArrPro) */ "#weak";
/*: (~pstrArr: {Arr(PStr)|(packed v)} > lArrPro) */ "#weak";

var exports = /*: Ref(~extern) */ "#extern";

var Object_ = /*: { getPrototypeOf: [;L,LP;] (o:Ref(L)) / (L: Dict > lObjPro)->
      { Ref(LP) | (implies (public o) (public v)) } / sameExact } */ "#extern";

var String = /*: (Top) -> Str */ "#extern";

var arrayIndexOf = /*: [;L1,L2;] (Ref(L1), Ref(L2)) 
                     / (L1: {Arr({(public v)})|(packed v)} > lArrPro, 
                        L2: {Arr({(public v)})|(packed v)} > lArrPro) 
                     -> {Int|(public v)} / sameExact */ "#extern";

var intToString = /*: ({Int|(public v)}) -> PStr */ "#extern";

var arraySlice = /*: [;L;] (Ref(L), Int, Int) 
                   / (L: {Arr({(public v)})|(packed v)} > lArrPro) 
                   -> Ref(L) / sameType */ "#extern";

//var arrayMap = /*: [;L;] (Ref(L), (Top) / (allFrozenLocations) -> PStr / sameType) 
//                     / (L: {Arr(Pub)|(packed v)} > lArrPro)
//                   -> Ref(L) / (L: {Arr(PStr)|(packed v)} > lArrPro) */ "#extern";

var arrayMap = /*: (Ref(~pubArr)) -> Ref(~pstrArr) */ "#extern";

var arrayJoin = /*: [;L;] (Ref(L), PStr) / (L: {Arr(PStr)|(packed v)} > lArrPro) -> PStr / sameExact */ "#extern";



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
/*: ({(public v)}) -> {Bool|(public v)} */ 
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
/*: (value: {(public v)}) -> {Bool|(and (iff (= v true) (Str value)) (public v))} */ 
{
  assert(/*: {(public v)} */ (typeof value));
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
/*: (value: {(public v)}) -> {Bool|(and (iff (= v true) (= (tag value) "function")) (public v))} */
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
/*: (value: {(public v)}) -> {Bool|(and (iff (= v true) (and (not (= value null)) (= (tag value) "object"))) (public v))} */
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
var isPrimitive = function isPrimitive(value) 
/*: (value: {(public v)}) -> {Bool|(public v)} */
{
  return !isFunction(value) && !isObject(value);
};
exports.isPrimitive = isPrimitive;

//TODO
///**
// * Returns `true` if given `object` is flat (it is direct decedent of
// * `Object.prototype` or `null`).
// * @examples
// *    isFlat({}) // true
// *    isFlat(new Type()) // false
// */
//var isFlat = function(object) 
///*: (object: {Ref(l)|(public v)}) / (l: { Dict|(public v)} > lObjPro) -> {Bool|(public v)} / sameExact */
//{
//  var f = Object_.getPrototypeOf;
//  assert(/*: {(public v)} */ ((/*: [;l,lObjPro;] */ f)(object)));
//  return isObject(object) ;// && (isNull((/*: [;l,lObjPro;] */ f)(object))  ||
//                              //isNull(Object_.getPrototypeOf(
//                                //     Object_.getPrototypeOf(object))));
//};
//exports.isFlat = isFlat;

/**
 * Returns `true` if object contains no values.
 */
/*
 *
 * I don't think we can prove anything more than the fact that the result is a
 * boolean. the key in the for...in statement is picked randomly and checked
 * against the contents of the object.
 *
 */
var isEmpty = function(object)
/*: (object: { Ref(lObj) | (public v)}) / 
    (lObj: Dict > lObjPro) -> Bool / sameType */
{
  if (isObject(object)) {
    var key /*: Str */ = "";
    var cnt /*: Bool */ = true;
    /*: ( lObj: Dict > lObjPro) -> sameType */
    for (key in object)
      cnt = false;
    return cnt;

    ////PV: original code
    //for (key in object) 
    //  return false;
    //return true;
  }
  return false;
};
exports.isEmpty = isEmpty;

/**
 * Returns `true` if `value` is an array / flat object containing only atomic
 * values and other flat objects.
 */
var isJSON = function(value, visited) 
/*: (value: {(public v)}, visited: Ref(lArr)) 
    / ( lArr: {Arr({(public v)})|(packed v)} > lArrPro)
    -> Top / sameType */ 
{
    // Adding value to array of visited values.
    var tmp = visited;
//    if (!tmp)
//      tmp = /*: lEmpty */ [];
    //Original code:
    //var tmp = visited || (visited = []);
    tmp.push(value);
            // If `value` is an atom return `true` cause it's valid JSON.
//    return  isPrimitive(value) ||
//            // If `value` is an array of JSON values that has not been visited
//            // yet.
//            (isArray(value) &&  value.every(function(element) {
//                                  return isJSON(element, visited);
//                                })) ||
//            // If `value` is a plain object containing properties with a JSON
//            // values it's a valid JSON.
//            (isFlat(value) && Object.keys(value).every(function(key) {
//                var $ = Object.getOwnPropertyDescriptor(value, key);
//                // Check every proprety of a plain object to verify that
//                // it's neither getter nor setter, but a JSON value, that
//                // has not been visited yet.
//                return  ((!isObject($.value) || !~visited.indexOf($.value)) &&
//                        !('get' in $) && !('set' in $) &&
//                        isJSON($.value, visited));
//            }));
};
//exports.isJSON = function (value) {
//  return isJSON(value);
//};

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
/*: {(and 
 
      (* (v:: (value: {(public v)}, Str, {Int|(public v)}, Str, Ref(lVis)) / (lVis: {Arr({(public v)})|(packed v)}) -> Top / sameType) *)

      (v:: (value: Ref(~pubArr), Str, {Int|(public v)}, Str, Ref(lVis)) 
        / (lVis: {Arr(Pub)|(packed v)} > lArrPro) -> Top / sameType)
        
    )} */
{
  var result;
  var names;
  var nestingIndex;
  var isCompact = !isUndefined(limit);

  indent = indent || "    ";
  offset = (offset || "");
  result = "";
  //visited = visited || [];

  if (isUndefined(value)) {
    result += "undefined";
  }
//  else if (isNull(value)) {
//    result += "null";
//  }
//  else if (isString(value)) {
//    result += '"' + value + '"';
//  }
//  else if (isFunction(value)) {
//    //TODO
//    //value = String(value).split("\n");
//    value = ["a", "b", "c"];
//    if (isCompact && value.length > 2) {
//      //TODO
//      //value = value.splice(0, 2);
//      value = ["a", "b"];
//      value.push("...}");
//    }
//    //TODO
//    //result += value.join("\n" + offset);
//    result += ("a\nb" + offset);
//  }
  else {

    /*: value lVal */ "#thaw";
    var cnd = isArray(value);
    /*: value (~pubArr, thwd lVal) */ "#freeze";
//    if (cnd) {
//    //PV: original code
//    //if ((nestingIndex = (visited.indexOf(value) + 1))) {
//    nestingIndex = /*: [;lVis, lVal;] */arrayIndexOf(visited, value) + 1;
//    if (nestingIndex) {
//      result = "#" + intToString(nestingIndex) + "#";
//      assert(/*: {(public v)} */ (result));
//    }
//    else {
//      visited.push(value);
//
//      if (isCompact)
//        value = /*: [;lVal;] */ arraySlice(value, 0, limit);
//
//      result += "[\n";
      //PV: original code:
      //result += value.map(function(value) {
      //  return offset + indent + 
      //    source_(value, indent, limit, offset + indent, visited);
      //}).join(",\n");
      
      var tmp1 = arrayMap(value
//          , 
//            function(value_) 
//            /*: (Top) -> PStr */ 
//            {
//              return "dummy";
//              //return offset + indent + 
//              //  source_(value_, indent, limit, offset + indent, visited);
//            }
          ) ; 
//      result += /*: [;lVal;] */ arrayJoin(tmp1, ",\n");
//      result += isCompact && value.length > limit ?
//                ",\n" + offset + "...]" : "\n" + offset + "]";
//    }
//    }
  }
//  else if (isObject(value)) {
//    if ((nestingIndex = (visited.indexOf(value) + 1))) {
//      result = "#" + nestingIndex + "#"
//    }
//    else {
//      visited.push(value)
//
//      names = Object.keys(value);
//
//      result += "{ // " + value + "\n";
//      result += (isCompact ? names.slice(0, limit) : names).map(function(name) {
//        var _limit = isCompact ? limit - 1 : limit;
//        var descriptor = Object.getOwnPropertyDescriptor(value, name);
//        var result = offset + indent + "// ";
//        var accessor;
//        if (0 <= name.indexOf(" "))
//          name = '"' + name + '"';
//
//        if (descriptor.writable)
//          result += "writable ";
//        if (descriptor.configurable)
//          result += "configurable ";
//        if (descriptor.enumerable)
//          result += "enumerable ";
//
//        result += "\n";
//        if ("value" in descriptor) {
//          result += offset + indent + name + ": ";
//          result += source(descriptor.value, indent, _limit, indent + offset,
//                           visited);
//        }
//        else {
//
//          if (descriptor.get) {
//            result += offset + indent + "get " + name + " ";
//            accessor = source(descriptor.get, indent, _limit, indent + offset,
//                              visited);
//            result += accessor.substr(accessor.indexOf("{"));
//          }
//
//          if (descriptor.set) {
//            result += offset + indent + "set " + name + " ";
//            accessor = source(descriptor.set, indent, _limit, indent + offset,
//                              visited);
//            result += accessor.substr(accessor.indexOf("{"));
//          }
//        }
//        return result;
//      }).join(",\n");
//
//      if (isCompact) {
//        if (names.length > limit && limit > 0) {
//          result += ",\n" + offset  + indent + "//...";
//        }
//      }
//      else {
//        if (names.length)
//          result += ",";
//
//        result += "\n" + offset + indent + '"__proto__": ';
//        result += source(Object.getPrototypeOf(value), indent, 0,
//                         offset + indent);
//      }
//
//      result += "\n" + offset + "}";
//    }
//  }
//  else {
//    result += String(value);
//  }
  return result;
};
//exports.source = function (value, indentation, limit) {
//  return source(value, indentation, limit);
//};


//assert(/*: {(public v)} */ (exports));
