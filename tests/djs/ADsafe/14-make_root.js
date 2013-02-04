/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";
var star    /*: Bool */         = "#extern";
var value     /*: Str */              = "#extern";       

var int_to_string /*: (Int) -> Str */ = "#extern";

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

//  var allow_focus /*: Bool */ = true,
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

    explode: explode

            //    fire: function (event) {
            //
            //      // Fire an event on an object. The event can be either
            //      // a string containing the name of the event, or an
            //      // object containing a type property containing the
            //      // name of the event. Handlers registered by the 'on'
            //      // method that match the event name will be invoked.
            //
            //      reject_global(this);
            //      var array,
            //          b,
            //          i,
            //          j,
            //          n,
            //          node,
            //          on,
            //          type;
            //
            //      if (typeof event === 'string') {
            //        type = event;
            //        event = {type: type};
            //      } else if (typeof event === 'object') {
            //        type = event.type;
            //      } else {
            //        error();
            //      }
            //      b = this.___nodes___;
            //      n = b.length;
            //      for (i = 0; i < n; i += 1) {
            //        node = b[i];
            //        on = node['___ on ___'];
            //
            //        // If an array of handlers exist for this event, then
            //        // loop through it and execute the handlers in order.
            //
            //        if (owns(on, type)) {
            //          array = on[type];
            //          for (j = 0; j < array.length; j += 1) {
            //
            //            // Invoke a handler. Pass the event object.
            //
            //            array[j].call(this, event);
            //          }
            //        }
            //      }
            //      return this;
            //    },
            //    focus: function () {
            //      reject_global(this);
            //      var b = this.___nodes___;
            //      if (b.length > 0 && allow_focus) {
            //        has_focus = b[0].focus();
            //        return this;
            //      }
            //      error();
            //    },
            //    fragment: function () {
            //      reject_global(this);
            //      return new Bunch([document.createDocumentFragment()]);
            //    },
            //    getCheck: function () {
            //      return this.getChecks()[0];
            //    },
            //    getChecks: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i].checked;
            //      }
            //      return a;
            //    },
            //    getClass: function () {
            //      return this.getClasses()[0];
            //    },
            //    getClasses: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i].className;
            //      }
            //      return a;
            //    },
            //    getMark: function () {
            //      return this.getMarks()[0];
            //    },
            //    getMarks: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i]['_adsafe mark_'];
            //      }
            //      return a;
            //    },
            //    getName: function () {
            //      return this.getNames()[0];
            //    },
            //    getNames: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i].name;
            //      }
            //      return a;
            //    },
            //    getOffsetHeight: function () {
            //      return this.getOffsetHeights()[0];
            //    },
            //    getOffsetHeights: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i].offsetHeight;
            //      }
            //      return a;
            //    },
            //    getOffsetWidth: function () {
            //      return this.getOffsetWidths()[0];
            //    },
            //    getOffsetWidths: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i].offsetWidth;
            //      }
            //      return a;
            //    },
            //    getParent: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i, n;
            //      for (i = 0; i < b.length; i += 1) {
            //        n = b[i].parentNode;
            //        if (n['___adsafe root___']) {
            //          error('ADsafe parent violation.');
            //        }
            //        a[i] = n;
            //      }
            //      return new Bunch(a);
            //    },
            //    getSelection: function () {
            //      reject_global(this);
            //      var b = this.___nodes___, end, node, start, range;
            //      if (b.length === 1 && allow_focus) {
            //        node = b[0];
            //        if (typeof node.selectionStart === 'number') {
            //          start = node.selectionStart;
            //          end = node.selectionEnd;
            //          return node.value.slice(start, end);
            //        }
            //        range = node.createTextRange();
            //        range.expand('textedit');
            //        if (range.inRange(the_range)) {
            //          return the_range.text;
            //        }
            //      }
            //      return null;
            //    },
            //    getStyle: function (name) {
            //      return this.getStyles(name)[0];
            //    },
            //    getStyles: function (name) {
            //      reject_global(this);
            //      if (reject_name(name)) {
            //        error("ADsafe style violation.");
            //      }
            //      var a = [], b = this.___nodes___, i, node, s;
            //      for (i = 0; i < b.length; i += 1) {
            //        node = b[i];
            //        if (node.tagName) {
            //          s = name !== 'float'
            //            ? getStyleObject(node)[name]
            //            : getStyleObject(node).cssFloat ||
            //            getStyleObject(node).styleFloat;
            //          if (typeof s === 'string') {
            //            a[i] = s;
            //          }
            //        }
            //      }
            //      return a;
            //    },
            //    getTagName: function () {
            //      return this.getTagNames()[0];
            //    },
            //    getTagNames: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i, name;
            //      for (i = 0; i < b.length; i += 1) {
            //        name = b[i].tagName;
            //        a[i] = typeof name === 'string' ? name.toLowerCase() : name;
            //      }
            //      return a;
            //    },
            //    getTitle: function () {
            //      return this.getTitles()[0];
            //    },
            //    getTitles: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        a[i] = b[i].title;
            //      }
            //      return a;
            //    },
            //    getValue: function () {
            //      return this.getValues()[0];
            //    },
            //    getValues: function () {
            //      reject_global(this);
            //      var a = [], b = this.___nodes___, i, node;
            //      for (i = 0; i < b.length; i += 1) {
            //        node = b[i];
            //        if (node.nodeName === '#text') {
            //          a[i] = node.nodeValue;
            //        } else if (node.tagName && node.type !== 'password') {
            //          a[i] = node.value;
            //          if (!a[i] && node.firstChild &&
            //              node.firstChild.nodeName === '#text') {
            //                a[i] = node.firstChild.nodeValue;
            //              }
            //        }
            //      }
            //      return a;
            //    },
            //    klass: function (value) {
            //      return this['class'](value);
            //    },
            //    mark: function (value) {
            //      reject_global(this);
            //      var b = this.___nodes___, i, node;
            //      if (value instanceof Array) {
            //        if (value.length !== b.length) {
            //          error('ADsafe: Array length: ' + b.length + '-' +
            //              value.length);
            //        }
            //        for (i = 0; i < b.length; i += 1) {
            //          node = b[i];
            //          if (node.tagName) {
            //            node['_adsafe mark_'] = String(value[i]);
            //          }
            //        }
            //      } else {
            //        for (i = 0; i < b.length; i += 1) {
            //          node = b[i];
            //          if (node.tagName) {
            //            node['_adsafe mark_'] = String(value);
            //          }
            //        }
            //      }
            //      return this;
            //    },
            //    off: function (type) {
            //      reject_global(this);
            //      var b = this.___nodes___, i, node;
            //      for (i = 0; i < b.length; i += 1) {
            //        node = b[i];
            //        if (typeof type === 'string') {
            //          if (typeof node['___ on ___']) {
            //            node['___ on ___'][type] = null;
            //          }
            //        } else {
            //          node['___ on ___'] = null;
            //        }
            //      }
            //      return this;
            //    },
            //    on: function (type, func) {
            //      reject_global(this);
            //      if (typeof type !== 'string' || typeof func !== 'function') {
            //        error();
            //      }
            //
            //      var b = this.___nodes___, i, node, on, ontype;
            //      for (i = 0; i < b.length; i += 1) {
            //        node = b[i];
            //
            //        // The change event does not propogate, so we must put the handler on the
            //        // instance.
            //
            //        if (type === 'change') {
            //          ontype = 'on' + type;
            //          if (node[ontype] !== dom_event) {
            //            node[ontype] = dom_event;
            //          }
            //        }
            //
            //        // Register an event. Put the function in a handler array, making one if it
            //        // doesn't yet exist for this type on this node.
            //
            //        on = node['___ on ___'];
            //        if (!on) {
            //          on = {};
            //          node['___ on ___'] = on;
            //        }
            //        if (owns(on, type)) {
            //          on[type].push(func);
            //        } else {
            //          on[type] = [func];
            //        }
            //      }
            //      return this;
            //    },
            //    protect: function () {
            //      reject_global(this);
            //      var b = this.___nodes___, i;
            //      for (i = 0; i < b.length; i += 1) {
            //        b[i]['___adsafe root___'] = '___adsafe root___';
            //      }
            //      return this;
            //    },
            //    q: function (text) {
            //      reject_global(this);
            //      star = this.___star___;
            //      return new Bunch(quest(parse_query(string_check(text), id),
            //            this.___nodes___));
            //    },
            //    remove: function () {
            //      reject_global(this);
            //      this.replace();
            //    },
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
