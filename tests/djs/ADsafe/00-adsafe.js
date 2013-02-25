// adsafe.js
// 2012-05-09

//    Public Domain.

//    NO WARRANTY EXPRESSED OR IMPLIED. USE AT YOUR OWN RISK.
//    SUBJECT TO CHANGE WITHOUT NOTICE.

//    Original url: http://www.ADsafe.org/adsafe.js

// This file implements the core ADSAFE runtime. A site may add additional
// methods understanding that those methods will be made available to guest
// code.

// This code should be minified before deployment.
// See http://javascript.crockford.com/jsmin.html

// USE YOUR OWN COPY. IT IS EXTREMELY UNWISE TO LOAD CODE FROM SERVERS YOU DO
// NOT CONTROL.

/*global window*/

/*jslint browser: true, devel: true, forin: true, nomen: true */

/*properties
    '', '#', '&', '*', '+', '.', '/', ':blur', ':checked', ':disabled',
    ':enabled', ':even', ':focus', ':hidden', ':odd', ':tag', ':text', ':trim',
    ':unchecked', ':visible', '>', '[', '[!=', '[$=', '[*=', '[=', '[^=', '[|=',
    '[~=', _, '___ on ___', '___adsafe root___', ___nodes___, ___star___,
    __defineGetter__, '_adsafe mark_', _intercept, a, abbr, acronym,
    addEventListener, address, altKey, append, appendChild, apply, area,
    arguments, autocomplete, b, bdo, big, blockquote, blur, br, bubble, button,
    call, callee, caller, cancelBubble, canvas, caption, center, change, charAt,
    charCode, check, checked, childNodes, cite, class, className, clientX,
    clientY, clone, cloneNode, code, col, colgroup, combine, concat, console,
    constructor, count, create, createDocumentFragment, createElement,
    createRange, createTextNode, createTextRange, cssFloat, ctrlKey,
    currentStyle, dd, defaultView, del, dfn, dir, disabled, div, dl, dt, each,
    em, empty, enable, ephemeral, eval, exec, expand, explode, fieldset, fire,
    firstChild, focus, font, form, fragment, fromCharCode, get, getCheck,
    getChecks, getClass, getClasses, getComputedStyle, getElementById,
    getElementsByTagName, getMark, getMarks, getName, getNames, getOffsetHeight,
    getOffsetHeights, getOffsetWidth, getOffsetWidths, getParent, getSelection,
    getStyle, getStyles, getTagName, getTagNames, getTitle, getTitles, getValue,
    getValues, go, h1, h2, h3, h4, h5, h6, has, hasOwnProperty, hr, i, id, img,
    inRange, indexOf, input, ins, insertBefore, isArray, kbd, key, keyCode, keys,
    klass, label, later, legend, length, li, lib, log, map, mark, menu, message,
    name, nextSibling, nodeName, nodeValue, object, off, offsetHeight,
    offsetWidth, ol, on, onclick, ondblclick, onfocusin, onfocusout, onkeypress,
    onmousedown, onmousemove, onmouseout, onmouseover, onmouseup, op, optgroup,
    option, p, parent, parentNode, postError, pre, prepend, preventDefault,
    protect, prototype, push, q, remove, removeChild, removeElement, replace,
    replaceChild, returnValue, row, samp, select, selection, selectionEnd,
    selectionStart, set, shiftKey, slice, small, span, srcElement, stack,
    stopPropagation, strong, style, styleFloat, sub, sup, table, tag, tagName,
    target, tbody, td, test, text, textarea, tfoot, th, that, thead, title,
    toLowerCase, toString, toUpperCase, tr, tt, type, u, ul, unwatch, value,
    valueOf, var, visibility, watch, window, writeln, x, y
*/


///////////////// DJS ////////////////////
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
var document  = /*: Ref(~lDocument) */ "#extern";
///////////////// DJS ////////////////////


var adsafe_id,      // The id of the current widget
    adsafe_lib,     // The script libraries loaded by the current widget

    // These member names are banned from guest scripts. The ADSAFE.get and
    // ADSAFE.put methods will not allow access to these properties.

    banned = /*: lBanned */ {
      'arguments'     : true,
      callee          : true,
      caller          : true,
      constructor     : true,
      'eval'          : true,
      prototype       : true,
      stack           : true,
      unwatch         : true,
      valueOf         : true,
      watch           : true
    },

    cache_style_object /*: Ref(~lStyle) */ = null,
    cache_style_node /*: Ref(~lNode) */ = null,
    defaultView = document.defaultView,
    ephemeral /*: Ref(~lBunch) */ = null;
    var flipflop /*: Bool */ = "#extern"; // Used in :even/:odd processing
    
    var has_focus /*: Ref(~lNode) */ = "#extern";

//    hunter,         // Set of hunter patterns
    var interceptors = [],

    makeableTagName = {

      // This is the whitelist of elements that may be created with the .tag(tagName)
      // method.

      a         : true,
      abbr      : true,
      acronym   : true,
      address   : true,
      area      : true,
      b         : true,
      bdo       : true,
      big       : true,
      blockquote: true,
      br        : true,
      button    : true,
      canvas    : true,
      caption   : true,
      center    : true,
      cite      : true,
      code      : true,
      col       : true,
      colgroup  : true,
      dd        : true,
      del       : true,
      dfn       : true,
      dir       : true,
      div       : true,
      dl        : true,
      dt        : true,
      em        : true,
      fieldset  : true,
      font      : true,
      form      : true,
      h1        : true,
      h2        : true,
      h3        : true,
      h4        : true,
      h5        : true,
      h6        : true,
      hr        : true,
      i         : true,
      img       : true,
      input     : true,
      ins       : true,
      kbd       : true,
      label     : true,
      legend    : true,
      li        : true,
      map       : true,
      menu      : true,
      object    : true,
      ol        : true,
      optgroup  : true,
      option    : true,
      p         : true,
      pre       : true,
      q         : true,
      samp      : true,
      select    : true,
      small     : true,
      span      : true,
      strong    : true,
      sub       : true,
      sup       : true,
      table     : true,
      tbody     : true,
      td        : true,
      textarea  : true,
      tfoot     : true,
      th        : true,
      thead     : true,
      tr        : true,
      tt        : true,
      u         : true,
      ul        : true,
      'var'     : true
    };
  
  var name /*: Str */ = "#extern";

//  var pecker;   // set of pecker patterns
  var result  /*: Ref(~lNodes) */ = "#extern";
  var star    /*: Bool */         = "#extern";
  var the_range /*: Ref(~lRange) */  = null;
  var value     /*: Str */              = "#extern";       

//  The error function is called if there is a violation or confusion.
//  It throws an exception.


var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";

//    Some of JavaScript's implicit string conversions can grant extraordinary
//    powers to untrusted code. So we use the string_check function to prevent
//    such abuses.

var string_check = /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

//    The object.hasOwnProperty method has a number of hazards. So we wrap it in
//    the owns function.

var owns = /*: (object: Ref, string: Str) 
             / (object: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
    { (implies (= v true) (has d {string}))} / sameType */ "#extern";


//  The reject functions enforce the restriction on property names.
//  reject_property allows access only to objects and arrays. It does not allow
//  use of the banned names, or names that are not strings and not numbers,
//  or strings that start or end with _.


//TODO: reject_name can have a more expressive type
var reject_name = /*: (name: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */ "#extern";


var reject_property = 
/*: (object: Top, name1: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */ "#extern";

var reject_global =
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */ "#extern";

var getStyleObject = /*: (node: Ref(~lNode)) -> Ref(~lStyle) */ "#extern";


var walkTheDOM = /*: ( node: Ref(~lNode), func:(Ref(~lNode)) -> Top, skip: Bool)
                   -> Top */ "#extern";

var purge_event_handlers = /*: (node: Ref(~lNode)) -> Top */ "#extern";

var parse_query = /*: (text: Str, id: Str) -> Ref(~lQuery) */ "#extern";

//TODO: changed names because string literals could not be parsed
var hunter = 
/*: {
  empty_  : (node       : Ref(~lNode)) / (&name   : Str) -> Top / sameExact,
  plus    : (node       : Ref(~lNode)) / (&name   : Str) -> Top / sameType,
  greater : (node       : Ref(~lNode)) / (&name   : Str) -> Top / sameType,
  pound   : () / (&name : Str) -> Top / sameType,
  slash   : (node       : Ref(~lNode)) -> Top,
  star    : (node       : Ref(~lNode)) / (&star   : Bool) -> Top / sameType
  } */ "#extern";


var pecker = 
  /*: {
    dot        : (Ref(~lNode)) -> Bool ,
    amber      : (Ref(~lNode)) -> Bool ,
    underscore : (Ref(~lNode)) -> Bool ,
    lbrack     : (Ref(~lNode)) -> Bool ,
    lbrackeq   : (Ref(~lNode)) -> Bool ,
    s1         : (Ref(~lNode)) -> Bool ,
    s2         : (Ref(~lNode)) -> Bool ,
    s3         : (Ref(~lNode)) -> Bool ,
    s4         : (Ref(~lNode)) -> Bool ,
    s5         : (Ref(~lNode)) -> Bool ,
    s6         : (Ref(~lNode)) -> Bool ,
    blur       : (Ref(~lNode)) -> Bool ,
    checked    : (Ref(~lNode)) -> Bool ,
    disabled   : (Ref(~lNode)) -> Top  ,
    enabled    : (Ref(~lNode)) -> Top  ,
    even       : (Ref(~lNode)) -> Bool ,
    focus      : (Ref(~lNode)) -> Bool ,
    hidden     : (Ref(~lNode)) -> Top  ,
    odd        : (Ref(~lNode)) -> Bool ,
    tag_       : (Ref(~lNode)) -> Str  ,
    text       : (Ref(~lNode)) -> Bool ,
    trim       : (Ref(~lNode)) -> Bool ,
    unchecked  : (Ref(~lNode)) -> Top  ,
    visible    : (Ref(~lNode)) -> Top
  } */ "#extern";


var quest = /*: (Ref(~lQuery), Ref(~lNodes)) -> Ref(~lNodes) */ "#extern";
          
var make_root = 
  /*: [;L;] (root:Ref(~lNode) , id:Str) / () -> 
      Ref(L) / (L: {Arr(Top) | 
                        (and 
                           (packed v) 
                           (= (len v) 2)
                           ({(v::Ref(~lDom))} (sel v 0))
                           ({(v::Ref(~lBunch))} (sel v 1))
                        )} > lArrPro) */ "#extern";

var go = /*: (id: Str, f: (Ref(~lDom), Ref(~lLib))-> Top ) -> Top */ "#extern";



/* START OF ADSAFE */ 
//TODO: Change "adsafe" to all capital.

/*: adsafe = () -> Top  */ "#type";
var adsafe = (function () {

  "use strict";

 
  function F() /*: (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ {
    //PV: added body
    return this;
  };

  var create = /*: (o:Ref, object: Ref) / (o: Dict > lObjPro, object: tyObject) -> Top / () */ "#extern";
  var get    = /*: (object: Ref, name: Str) / (object: Dict > lObjPro) -> Top / sameType */ "#extern";
  var has_   = /*: (object: Ref, name: Str) 
                 / (object: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
                  { (implies (= v true) (has d {name}))} / sameType */ "#extern";
  var id     = /*: (id: Ref(~lId)) -> Top */ "#extern";
  var isArray_ = /*: (Top) -> Bool */ "#extern";
  var keys = /*: (object:Ref) 
               / (object: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) 
               -> Ref(~lKeys) / sameType */ "#extern";
  var later = /*: (func: Top, timeout: Int) -> Top */ "#extern";
  var lib = /*: (Str, (Ref(~lLib)) -> Top) -> Top */ "#extern";
  var log = /*: (Str) -> Top */ "#extern";
  var remove = /*: (object: Ref, name: Str) / (object: d: Dict > lObjPro) -> Top / sameType */ "#extern";
  var set = /*: (object: Ref, name: Str, value: Str) 
    / (object: d: Dict > lObjPro, lArr: {Arr(Str)|(packed v)} > lArrPro) 
    -> Top / sameType */ "#extern";
  var _intercept = /*: (f: {(= (tag v) "function")}) -> Top */ "#extern";

  var adsafe_ = {
          create: create,
          get: get,
          go: go, 
          has: has_,
          id: id,
          isArray: isArray_,
          keys: keys,
          later: later, 
          lib: lib,
          log: log,
          remove: remove,
          set: set,
          _intercept: _intercept
      };

  //  Return the ADSAFE object.
  
  return adsafe_;

}/*()*/);
