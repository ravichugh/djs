/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";
var star    /*: Bool */         = "#extern";
var value     /*: Str */              = "#extern";       

var int_to_string /*: (Int) -> Str */ = "#extern";

     

var make_root = function(root, id)
  /*: (root:Ref(~lNode) , id:Str) -> Top */ 
{

  if (id) {
    if (root.tagName !== 'DIV') {
      error('ADsafe: Bad node.');
    }
  } else {
    if (root.tagName !== 'BODY') {
      error('ADsafe: Bad node.');
    }
  };

  // A Bunch is a container that holds zero or more dom nodes.
  // It has many useful methods.

  function Bunch(nodes)
    /*: new (this:Ref, nodes: Ref(~lNodes)) / (this: Empty > lBunchProto, ~lBunch: frzn) ->
      Ref(~lBunch) / (~lBunch: frzn) */
  {
    this.___nodes___ = nodes;
    /*: nodes lNodes */ "#thaw";
    this.___star___ = star && nodes.length > 1;
    /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
    star = false;
    var self = this;
    /*: self (~lBunch,frzn) */ "#freeze";
    return self;      //PV: added return
  };

  var allow_focus /*: Bool */ = true;
//      dom,
//      dom_event = function (event,e) 
//        /*: (event: Ref(~lEvent), e: Ref(~lEvent)) -> Top */
//      {
//        var key /*: Str */ = "";
//        var the_actual_event = e || event;
//        var type /*: Str */ = the_actual_event.type;
//
//        // Get the target node and wrap it in a bunch.
//
//        var the_target /*: Ref(~lNode) */ = the_actual_event.target || the_actual_event.srcElement;
//
//        var tt = /*: lTT Arr(Ref(~lNode)) */ [the_target];
//        /*: tt (~lNodes, frzn) */ "#freeze";
//
//        var target = new Bunch(tt);
//        var that = target;
//
//        // Use the PPK hack to make focus bubbly on IE.
//        // When a widget has focus, it can use the focus method.
//
//        switch (type) {
//          case 'mousedown':
//            allow_focus = true;
//            if (document.selection) {
//              the_range = document.selection.createRange();
//            }
//            break;
//          case 'focus':
//          case 'focusin':
//            allow_focus = true;
//            has_focus = the_target;
//            the_actual_event.cancelBubble = false;
//            type = 'focus';
//            break;
//          case 'blur':
//          case 'focusout':
//            allow_focus = false;
//            has_focus = null;
//            type = 'blur';
//            break;
//          case 'keypress':
//            allow_focus = true;
//            has_focus = the_target;
//            //TODO: Add String.fromCharCode to prims                        
//              key = String.fromCharCode(the_actual_event.charCode || the_actual_event.keyCode);
//            switch (key) {
//              case '\u000d':
//              case '\u000a':
//                type = 'enterkey';
//                break;
//              case '\u001b':
//                type = 'escapekey';
//                break;
//            }
//            break;
//
//            // This is a workaround for Safari.
//
//          case 'click':
//            allow_focus = true;
//            break;
//        }
//
//        if (the_actual_event.cancelBubble &&
//            the_actual_event.stopPropagation) {
//              the_actual_event.stopPropagation();
//            }
//
//        // Make the event object.
//
//        var the_event = {
//          altKey: the_actual_event.altKey,
//          ctrlKey: the_actual_event.ctrlKey,
//          //TODO: try-catch                          
//          bubble: function () 
//            /*: () -> Top */
//          {
//
//            // Bubble up. Get the parent of that node. It becomes the new that.
//            // getParent throws when bubbling is not possible.
//
//            try {
//              var parent = that.getParent(),
//              b = parent.___nodes___[0];
//              that = parent;
//              the_event.that = that;
//
//              // If that node has an event handler, fire it. Otherwise, bubble up.
//
//              if (b['___ on ___'] &&
//                  b['___ on ___'][type]) {
//                    that.fire(the_event);
//                  } else {
//                    the_event.bubble();
//                  }
//            } catch (e) {
//              error(e);
//            }
//          },                        
//          key: key,
//          preventDefault: function () {
//            if (the_actual_event.preventDefault) {
//              the_actual_event.preventDefault();
//            }
//            the_actual_event.returnValue = false;
//          },
//          shiftKey: the_actual_event.shiftKey,
//          target: target,
//          //                        that: that,
//          type: type,
//          x: the_actual_event.clientX,
//          y: the_actual_event.clientY
//        };
//
//
//        // if the target has event handlers, then fire them. otherwise, bubble up.
//
//        if (the_target['___ on ___'] &&
//            the_target['___ on ___'][the_event.type]) {
//              //                        target.fire(the_event);
//            } 
//        else {
//          for (;;) {
//            the_target = the_target.parentNode;
//            if (!the_target) {
//              //break;
//            }
//            if (the_target['___ on ___'] &&
//                the_target['___ on ___'][the_event.type]) {
//                  that = new Bunch([the_target]);
//                  the_event.that = that;
//                  that.fire(the_event);
//                  break;
//                }
//            if (the_target['___adsafe root___']) {
//              break;
//            }
//          }
//        }
//        if (the_event.type === 'escapekey') {
//          if (ephemeral) {
//            ephemeral.remove();
//          }
//          ephemeral = null;
//        }
//        that = the_target = the_event = the_actual_event = null;
//        return;
//      };
//
//  // Mark the node as a root. This prevents event bubbling from propagating
//  // past it.
//
//  root['___adsafe root___'] = '___adsafe root___';
//

  var  append = 
  /*: (this: Ref(~lBunch), appendage: Ref(lArr)) 
      / (lArr: Arr(Ref(~lBunch)) > lArrPro) -> Top / sameType */
      "#extern";
   
  var blur = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";

  var check  = 
  /*: {(and
      (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(NotUndef) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
      (v :: (this: Ref(~lBunch), value: Ref) / (value: {} > lObjPro) -> Ref(~lBunch) / sameType) 
      ) } */ "#extern";

  var class_fun =
  /*: {(and
      (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
      (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch) ) 
      )} */ "#extern";


  var clone = /*: (this: Ref(~lBunch), deep:Bool, n: Num) -> Top */ "#extern";

  var count = /*: (this: Ref(~lBunch)) -> Int */ "#extern";

  var each = /*: (this: Ref(~lBunch), func: (Ref(~lBunch)) -> Top) -> Top */ "#extern";

  var empty = 
  /*: {(and
      (v :: (this: Ref(~lBunch)) / (&value: Ref(lArr), lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
      (v :: (this: Ref(~lBunch)) / (&value: Ref(lObj), lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType)
      )} */ "#extern";

  var enable = 
  /*: {(and
      (v :: (this: Ref(~lBunch), enable: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
      (v :: (this: Ref(~lBunch), enable: Ref(lObj)) / (lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType))} */ "#extern";

  var ephemeral = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";

  var explode = /*: [;L;] (this: Ref(~lBunch)) / () -> Ref(L) / (L: Arr(Ref(~lBunch)) > lArrPro) */ "#extern";

  var fire = 
  /*: {(and
      (v :: (this: Ref(~lBunch), event: Str) -> Ref(~lBunch))
      (v :: (this: Ref(~lBunch), event: Ref(~lEvent)) -> Ref(~lBunch)))} */ "#extern";

  var focus = /*: (this: Ref(~lBunch)) / (&has_focus: Top) -> Top / sameType*/ "#extern";
  var fragment = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";
  var getCheck = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getChecks = /*: (this: Ref(~lBunch)) -> Ref(~lChecked) */ "#extern";
  var getClass = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getClasses = /*: (this: Ref(~lBunch)) -> Ref(~lClassNames) */ "#extern";
  var getMark = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getMarks = /*: (this: Ref(~lBunch)) -> Ref(~lADsafeMarks) */ "#extern";
  var getName =  /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getNames = /*: (this: Ref(~lBunch)) -> Ref(~lNames) */ "#extern";
  var getOffsetHeight =  /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getOffsetHeights = /*: (this: Ref(~lBunch)) -> Ref(~lOffsetHeights) */ "#extern";
  var getOffsetWidth =  /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getOffsetWidths = /*: (this: Ref(~lBunch)) -> Ref(~lOffsetWidths) */ "#extern";
  var getParent =  /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";
  var getSelection =  /*: (this: Ref(~lBunch)) -> {(or (Str v) (= v null))} */ "#extern";
  var getStyle =  /*: (this: Ref(~lBunch), Str) -> Top */ "#extern";
  var getStyles = /*: (this: Ref(~lBunch), Str) -> Ref(~lStyles) */ "#extern";
  var getTagName = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getTagNames = /*: (this: Ref(~lBunch)) -> Ref(~lNames) */ "#extern";
  var getTitle =  /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getTitles = /*: (this: Ref(~lBunch)) -> Ref(~lNames) */ "#extern";
  var getValue =  /*: (this: Ref(~lBunch)) -> Top */ "#extern";
  var getValues = /*: (this: Ref(~lBunch)) -> Ref(~lValues) */ "#extern";
 
  var klass = /*: (this: Ref(~lBunch), value: Str) -> Top */ "#extern";

  var mark =
  /*: {(and
      (v :: (this: Ref(~lBunch), value: Ref(lArr)) 
        / (lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
      (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch)) )} */ "#extern";

  var off = /*: (this: Ref(~lBunch), type_:Top) -> Ref(~lBunch) */ "#extern";

  var on = /*: (this: Ref(~lBunch), type_:Top, func: (Top) -> Top) -> Ref(~lBunch) */ "#extern";

  var protect = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";

  var q = /*: (this: Ref(~lBunch), Str) -> Ref(~lBunch) */ "#extern";

  var remove = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
    
  Bunch.prototype = {

    append: append,
      
    blur: blur,

    check: check,

    'class': class_fun,

    clone: clone,
    
    count: count,
    
    each: each,
    
    empty: empty,
      
    enable: enable,
    
    ephemeral: ephemeral,

    explode: explode,

    fire: fire,

    focus: focus,
    
    fragment: fragment,
      
    getCheck: getCheck, 
    
    getClass: getClass,
    
    getClasses: getClasses,
    
    getMark: getMark,
    
    getMarks: getMarks,
    
    getName: getName,
    
    getNames: getNames,
    
    getOffsetHeight: getOffsetHeight,
    
    getOffsetHeights: getOffsetHeights, 
    
    getOffsetWidth: getOffsetWidth,

    getOffsetWidths: getOffsetWidths,
    
    getParent: getParent,
    
    getSelection: getSelection,
    
    getStyle: getStyle,
    
    getStyles: getStyles,
    
    getTagName: getTagName,
    
    getTagNames: getTagNames,
    
    getTitle: getTitle,
    
    getTitles: getTitles,
    
    getValue: getValue,
    
    getValues: getValues,

    klass: klass,
    
    mark: mark,
    
    off: off,
    
    on: on,

    protect: protect,
      
    q: q,
    
    remove: remove
      
//    replace: function (replacement) {
    //      reject_global(this);
    //      var b = this.___nodes___,
    //          flag = false,
    //          i,
    //          j,
    //          newnode,
    //          node,
    //          parent,
    //          rep;
    //      if (b.length === 0) {
    //        return;
    //      }
    //      for (i = 0; i < b.length; i += 1) {
    //        purge_event_handlers(b[i]);
    //      }
    //      if (!replacement || replacement.length === 0 ||
    //          (replacement.___nodes___ &&
    //           replacement.___nodes___.length === 0)) {
    //             for (i = 0; i < b.length; i += 1) {
    //               node = b[i];
    //               purge_event_handlers(node);
    //               if (node.parentNode) {
    //                 node.parentNode.removeChild(node);
    //               }
    //             }
    //           } else if (replacement instanceof Array) {
    //             if (replacement.length !== b.length) {
    //               error('ADsafe: Array length: ' +
    //                   b.length + '-' + value.length);
    //             }
    //             for (i = 0; i < b.length; i += 1) {
    //               node = b[i];
    //               parent = node.parentNode;
    //               purge_event_handlers(node);
    //               if (parent) {
    //                 rep = replacement[i].___nodes___;
    //                 if (rep.length > 0) {
    //                   newnode = rep[0];
    //                   parent.replaceChild(newnode, node);
    //                   for (j = 1; j < rep.length; j += 1) {
    //                     node = newnode;
    //                     newnode = rep[j];
    //                     parent.insertBefore(newnode, node.nextSibling);
    //                   }
    //                 } else {
    //                   parent.removeChild(node);
    //                 }
    //               }
    //             }
    //           } else {
    //             rep = replacement.___nodes___;
    //             for (i = 0; i < b.length; i += 1) {
    //               node = b[i];
    //               purge_event_handlers(node);
    //               parent = node.parentNode;
    //               if (parent) {
    //                 newnode = flag ? rep[0].cloneNode(true) : rep[0];
    //                 parent.replaceChild(newnode, node);
    //                 for (j = 1; j < rep.length; j += 1) {
    //                   node = newnode;
    //                   newnode = flag ? rep[j].clone(true) : rep[j];
    //                   parent.insertBefore(newnode, node.nextSibling);
    //                 }
    //                 flag = true;
    //               }
    //             }
    //           }
    //      return this;
    //    },
    //    select: function () {
    //      reject_global(this);
    //      var b = this.___nodes___;
    //      if (b.length < 1 || !allow_focus) {
    //        error();
    //      }
    //      b[0].focus();
    //      b[0].select();
    //      return this;
    //    },
    //    selection: function (string) {
    //      reject_global(this);
    //      string_check(string);
    //      var b = this.___nodes___, end, node, old, start, range;
    //      if (b.length === 1 && allow_focus) {
    //        node = b[0];
    //        if (typeof node.selectionStart === 'number') {
    //          start = node.selectionStart;
    //          end = node.selectionEnd;
    //          old = node.value;
    //          node.value = old.slice(0, start) + string + old.slice(end);
    //          node.selectionStart = node.selectionEnd = start +
    //            string.length;
    //          node.focus();
    //        } else {
    //          range = node.createTextRange();
    //          range.expand('textedit');
    //          if (range.inRange(the_range)) {
    //            the_range.select();
    //            the_range.text = string;
    //            the_range.select();
    //          }
    //        }
    //      }
    //      return this;
    //    },
    //    style: function (name, value) {
    //      reject_global(this);
    //      if (reject_name(name)) {
    //        error("ADsafe style violation.");
    //      }
    //      if (value === undefined || /url/i.test(string_check(value))) {
    //        error();
    //      }
    //      var b = this.___nodes___,
    //          i,
    //          node,
    //          v;
    //      if (value instanceof Array) {
    //        if (value.length !== b.length) {
    //          error('ADsafe: Array length: ' +
    //              b.length + '-' + value.length);
    //        }
    //        for (i = 0; i < b.length; i += 1) {
    //          node = b[i];
    //          v = string_check(value[i]);
    //          if (/url/i.test(v)) {
    //            error();
    //          }
    //          if (node.tagName) {
    //            if (name !== 'float') {
    //              node.style[name] = v;
    //            } else {
    //              node.style.cssFloat = node.style.styleFloat = v;
    //            }
    //          }
    //        }
    //      } else {
    //        v = string_check(value);
    //        if (/url/i.test(v)) {
    //          error();
    //        }
    //        for (i = 0; i < b.length; i += 1) {
    //          node = b[i];
    //          if (node.tagName) {
    //            if (name !== 'float') {
    //              node.style[name] = v;
    //            } else {
    //              node.style.cssFloat = node.style.styleFloat = v;
    //            }
    //          }
    //        }
    //      }
    //      return this;
    //    },
    //    tag: function (tag, type, name) {
    //      reject_global(this);
    //      var node;
    //      if (typeof tag !== 'string') {
    //        error();
    //      }
    //      if (makeableTagName[tag] !== true) {
    //        error('ADsafe: Bad tag: ' + tag);
    //      }
    //      node = document.createElement(tag);
    //      if (name) {
    //        node.autocomplete = 'off';
    //        node.name = string_check(name);
    //      }
    //      if (type) {
    //        node.type = string_check(type);
    //      }
    //      return new Bunch([node]);
    //    },
    //    text: function (text) {
    //      reject_global(this);
    //      var a, i;
    //      if (text instanceof Array) {
    //        a = [];
    //        for (i = 0; i < text.length; i += 1) {
    //          a[i] = document.createTextNode(string_check(text[i]));
    //        }
    //        return new Bunch(a);
    //      }
    //      return new Bunch([document.createTextNode(string_check(text))]);
    //    },
    //    title: function (value) {
    //      reject_global(this);
    //      var b = this.___nodes___, i, node;
    //      if (value instanceof Array) {
    //        if (value.length !== b.length) {
    //          error('ADsafe: Array length: ' + b.length +
    //              '-' + value.length);
    //        }
    //        for (i = 0; i < b.length; i += 1) {
    //          node = b[i];
    //          if (node.tagName) {
    //            node.title = string_check(value[i]);
    //          }
    //        }
    //      } else {
    //        string_check(value);
    //        for (i = 0; i < b.length; i += 1) {
    //          node = b[i];
    //          if (node.tagName) {
    //            node.title = value;
    //          }
    //        }
    //      }
    //      return this;
    //    },
    //    value: function (value) {
    //      reject_global(this);
    //      if (value === undefined) {
    //        error();
    //      }
    //      var b = this.___nodes___, i, node;
    //      if (value instanceof Array && b.length === value.length) {
    //        for (i = 0; i < b.length; i += 1) {
    //          node = b[i];
    //          if (node.tagName) {
    //            if (node.type !== 'password') {
    //              if (typeof node.value === 'string') {
    //                node.value = value[i];
    //              } else {
    //                while (node.firstChild) {
    //                  purge_event_handlers(node.firstChild);
    //                  node.removeChild(node.firstChild);
    //                }
    //                node.appendChild(document.createTextNode(
    //                      String(value[i])
    //                      ));
    //              }
    //            }
    //          } else if (node.nodeName === '#text') {
    //            node.nodeValue = String(value[i]);
    //          }
    //        }
    //      } else {
    //        value = String(value);
    //        for (i = 0; i < b.length; i += 1) {
    //          node = b[i];
    //          if (node.tagName) {
    //            if (node.tagName !== 'BUTTON' &&
    //                typeof node.value === 'string') {
    //                  node.value = value;
    //                } else {
    //                  while (node.firstChild) {
    //                    purge_event_handlers(node.firstChild);
    //                    node.removeChild(node.firstChild);
    //                  }
    //                  node.appendChild(document.createTextNode(value));
    //                }
    //          } else if (node.nodeName === '#text') {
    //            node.nodeValue = value;
    //          }
    //        }
    //      }
    //      return this;
    //    }
  };
  //
  //  // Return an ADsafe dom object.
  //
  //  dom = {
  //    append: function (bunch) {
  //      var b = bunch.___nodes___, i, n;
  //      for (i = 0; i < b.length; i += 1) {
  //        n = b[i];
  //        if (typeof n === 'string' || typeof n === 'number') {
  //          n = document.createTextNode(String(n));
  //        }
  //        root.appendChild(n);
  //      }
  //      return dom;
  //    },
  //    combine: function (array) {
  //      if (!array || !array.length) {
  //        error('ADsafe: Bad combination.');
  //      }
  //      var b = array[0].___nodes___, i;
  //      for (i = 0; i < array.length; i += 1) {
  //        b = b.concat(array[i].___nodes___);
  //      }
  //      return new Bunch(b);
  //    },
  //    count: function () {
  //      return 1;
  //    },
  //    ephemeral: function (bunch) {
  //      if (ephemeral) {
  //        ephemeral.remove();
  //      }
  //      ephemeral = bunch;
  //      return dom;
  //    },
  //    fragment: function () {
  //      return new Bunch([document.createDocumentFragment()]);
  //    },
  //    prepend: function (bunch) {
  //      var b = bunch.___nodes___, i;
  //      for (i = 0; i < b.length; i += 1) {
  //        root.insertBefore(b[i], root.firstChild);
  //      }
  //      return dom;
  //    },
  //    q: function (text) {
  //      star = false;
  //      var query = parse_query(text, id);
  //      if (typeof hunter[query[0].op] !== 'function') {
  //        error('ADsafe: Bad query: ' + query[0]);
  //      }
  //      return new Bunch(quest(query, [root]));
  //    },
  //    remove: function () {
  //      purge_event_handlers(root);
  //      root.parent.removeElement(root);
  //      root = null;
  //    },
  //    row: function (values) {
  //      var tr = document.createElement('tr'),
  //      td,
  //      i;
  //      for (i = 0; i < values.length; i += 1) {
  //        td = document.createElement('td');
  //        td.appendChild(document.createTextNode(String(values[i])));
  //        tr.appendChild(td);
  //      }
  //      return new Bunch([tr]);
  //    },
  //    tag: function (tag, type, name) {
  //      var node;
  //      if (typeof tag !== 'string') {
  //        error();
  //      }
  //      if (makeableTagName[tag] !== true) {
  //        error('ADsafe: Bad tag: ' + tag);
  //      }
  //      node = document.createElement(tag);
  //      if (name) {
  //        node.autocomplete = 'off';
  //        node.name = name;
  //      }
  //      if (type) {
  //        node.type = type;
  //      }
  //      return new Bunch([node]);
  //    },
  //    text: function (text) {
  //      var a, i;
  //      if (text instanceof Array) {
  //        a = [];
  //        for (i = 0; i < text.length; i += 1) {
  //          a[i] = document.createTextNode(string_check(text[i]));
  //        }
  //        return new Bunch(a);
  //      }
  //      return new Bunch([document.createTextNode(string_check(text))]);
  //    }
  //  };
  //
  //  if (typeof root.addEventListener === 'function') {
  //    root.addEventListener('focus', dom_event, true);
  //    root.addEventListener('blur', dom_event, true);
  //    root.addEventListener('mouseover', dom_event, true);
  //    root.addEventListener('mouseout', dom_event, true);
  //    root.addEventListener('mouseup', dom_event, true);
  //    root.addEventListener('mousedown', dom_event, true);
  //    root.addEventListener('mousemove', dom_event, true);
  //    root.addEventListener('click', dom_event, true);
  //    root.addEventListener('dblclick', dom_event, true);
  //    root.addEventListener('keypress', dom_event, true);
  //  } else {
  //    root.onfocusin       = root.onfocusout  = root.onmouseout  =
  //      root.onmousedown = root.onmousemove = root.onmouseup   =
  //      root.onmouseover = root.onclick     = root.ondblclick  =
  //      root.onkeypress  = dom_event;
  //  }
  //  return [dom, Bunch.prototype];
};
