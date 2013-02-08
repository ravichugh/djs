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

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

//    The object.hasOwnProperty method has a number of hazards. So we wrap it in
//    the owns function.
//TODO: TC owns
//    var owns = /*: (object, string) */ "#extern";


//  The reject functions enforce the restriction on property names.
//  reject_property allows access only to objects and arrays. It does not allow
//  use of the banned names, or names that are not strings and not numbers,
//  or strings that start or end with _.


//TODO: reject_name can have a more expressive type
var reject_name = /*: (name1: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */ "#extern";


var reject_property = 
/*: (object: Top, name1: Str) / (lBanned:Dict > lObjPro) -> Top / sameExact */ "#extern";

//TODO: TC reject_global
//var reject_global(that) = /*: ... */ "#extern";


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
          
var make_root = /*: (root:Ref(~lNode) , id:Str) -> Top */ "#extern";




/* START OF ADSAFE */ 
//TODO: Change "adsafe" to all capital.

/*: adsafe = () -> Top  */ "#type";
var adsafe = (function () {

  "use strict";

  //
  //
  //    function F() {}
  //
  //
  ////  Return the ADSAFE object.
  //
  //    return {
  //
  //        create: function (o) {
  //            reject_global(o);
  //            if (Object.hasOwnProperty('create')) {
  //                return Object.create(o);
  //            }
  //            F.prototype = typeof o === 'object' && o ? o : Object.prototype;
  //            return new F();
  //        },
  //
  ////  ADSAFE.get retrieves a value from an object.
  //
  //        get: function (object, name) {
  //            reject_global(object);
  //            if (arguments.length === 2 && !reject_property(object, name)) {
  //                return object[name];
  //            }
  //            error();
  //        },
  //
  ////  ADSAFE.go allows a guest widget to get access to a wrapped dom node and
  ////  approved ADsafe libraries. It is passed an id and a function. The function
  ////  will be passed the wrapped dom node and an object containing the libraries.
  //
  //        go: function (id, f) {
  //            var dom, fun, root, i, scripts;
  //
  ////  If ADSAFE.id was called, the id better match.
  //
  //            if (adsafe_id && adsafe_id !== id) {
  //                error();
  //            }
  //
  ////  Get the dom node for the widget's div container.
  //
  //            root = document.getElementById(id);
  //            if (root.tagName !== 'DIV') {
  //                error();
  //            }
  //            adsafe_id = null;
  //
  ////  Delete the scripts held in the div. They have all run, so we don't need
  ////  them any more. If the div had no scripts, then something is wrong.
  ////  This provides some protection against mishaps due to weakness in the
  ////  document.getElementById function.
  //
  //            scripts = root.getElementsByTagName('script');
  //            i = scripts.length - 1;
  //            if (i < 0) {
  //                error();
  //            }
  //            do {
  //                root.removeChild(scripts[i]);
  //                i -= 1;
  //            } while (i >= 0);
  //            root = make_root(root, id);
  //            dom = root[0];
  //
  //
  //// If the page has registered interceptors, call then.
  //
  //            for (i = 0; i < interceptors.length; i += 1) {
  //                fun = interceptors[i];
  //                if (typeof fun === 'function') {
  //                    try {
  //                        fun(id, dom, adsafe_lib, root[1]);
  //                    } catch (e1) {
  //                        ADSAFE.log(e1);
  //                    }
  //                }
  //            }
  //
  ////  Call the supplied function.
  //
  //            try {
  //                f(dom, adsafe_lib);
  //            } catch (e2) {
  //                ADSAFE.log(e2);
  //            }
  //            root = null;
  //            adsafe_lib = null;
  //        },
  //
  ////  ADSAFE.has returns true if the object contains an own property with the
  ////  given name.
  //
  //        has: function (object, name) {
  //            return owns(object, name);
  //        },
  //
  ////  ADSAFE.id allows a guest widget to indicate that it wants to load
  ////  ADsafe approved libraries.
  //
  //        id: function (id) {
  //
  ////  Calls to ADSAFE.id must be balanced with calls to ADSAFE.go.
  ////  Only one id can be active at a time.
  //
  //            if (adsafe_id) {
  //                error();
  //            }
  //            adsafe_id = id;
  //            adsafe_lib = {};
  //        },
  //
  ////  ADSAFE.isArray returns true if the operand is an array.
  //
  //        isArray: Array.isArray || function (value) {
  //            return Object.prototype.toString.apply(value) === '[object Array]';
  //        },
  //
  //
  //
  ////  ADSAFE.keys returns an array of keys.
  //
  //        keys: Object.keys || function (object) {
  //            var key, result = [];
  //            for (key in object) {
  //                if (owns(object, key)) {
  //                    result.push(key);
  //                }
  //            }
  //            return result;
  //        },
  //
  //
  ////  ADSAFE.later calls a function at a later time.
  //
  //        later: function (func, timeout) {
  //            if (typeof func === 'function') {
  //                setTimeout(func, timeout || 0);
  //            } else {
  //                error();
  //            }
  //        },
  //
  //
  ////  ADSAFE.lib allows an approved ADsafe library to make itself available
  ////  to a widget. The library provides a name and a function. The result of
  ////  calling that function will be made available to the widget via the name.
  //
  //        lib: function (name, f) {
  //            if (!adsafe_id || reject_name(name)) {
  //                error("ADsafe lib violation.");
  //            }
  //            adsafe_lib[name] = f(adsafe_lib);
  //        },
  //
  //
  ////  ADSAFE.log is a debugging aid that spams text to the browser's log.
  ////  Overwrite this function to send log matter somewhere else.
  //
  //        log: function log(s) {
  //            if (window.console) {
  //                console.log(s);        /* Firebug */
  //            } else if (typeof Debug === 'object') {
  //                Debug.writeln(s);      /* IE */
  //            } else if (typeof opera === 'opera') {
  //                opera.postError(s);    /* Opera */
  //            }
  //        },
  //
  //
  ////  ADSAFE.remove deletes a value from an object.
  //
  //        remove: function (object, name) {
  //            if (arguments.length === 2 && !reject_property(object, name)) {
  //                delete object[name];
  //                return;
  //            }
  //            error();
  //        },
  //
  //
  ////  ADSAFE.set stores a value in an object.
  //
  //        set: function (object, name, value) {
  //            reject_global(object);
  //            if (arguments.length === 3 && !reject_property(object, name)) {
  //                object[name] = value;
  //                return;
  //            }
  //            error();
  //        },
  //
  ////  ADSAFE._intercept allows the page to register a function that will
  ////  see the widget's capabilities.
  //
  //        _intercept: function (f) {
  //            interceptors.push(f);
  //        }
  //
  //    };
}/*()*/);
