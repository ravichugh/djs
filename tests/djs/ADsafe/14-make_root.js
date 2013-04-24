/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document  = /*: Ref(~lDocument) */ "#extern";
var error = /*: (message: Str)  -> { FLS } */ "#extern";

var int_to_string = /*: (Int) -> Str */ "#extern";

var stringFromCharCode = /*: (Int) -> Str */ "#extern";


var star          /*: Bool */ = "#extern";
var value         /*: Str */  = "#extern";       
var event         /*: Ref(~lEvent) */ = "#extern";

var the_range /*: Ref(~lRange) */  = null;
    
var has_focus /*: Ref(~htmlElt) */ = "#extern";

var the_event /*: Ref(~lEvent) */ = "#extern";

var ephemeral /*: {(or (= v null) (v:: Ref(~lBunch)))} */ = "#extern";

var make_root = function(root, id) 
  /* [;L;] (root:Ref(~htmlElt) , id:Str) / () -> 
      Ref(L) / (L: {Arr(Top) | 
                        (and 
                           (packed v) 
                           (= (len v) 2)
                           ({(v::Ref(~lDom))} (sel v 0))
                           ({(v::Ref(lBunchProto))} (sel v 1))
                        )} > lArrPro) */
  /*: [;L;] (root:Ref(~htmlElt) , id:Str) ->  Top */

{
//TODO: SLOW DOWN !!! ~ 11 sec
//  /*: root lhtmlElt */ "#thaw";
//  assume(root != null);
//  if (id) {
//    if (root.tagName !== 'DIV') {
//      error('ADsafe: Bad node.');
//    }
//  } else {
//    if (root.tagName !== 'BODY') {
//      error('ADsafe: Bad node.');
//    }
//  };
//  /*: root (~htmlElt, thwd lhtmlElt) */ "#freeze";

  // A Bunch is a container that holds zero or more dom nodes.
  // It has many useful methods.

  function Bunch(nodes)
    /*: new (this:Ref, nodes: Ref(~htmlElts)) / (this: Empty > lBunchProto) -> Ref(~lBunch) / () */
  {
    this.___nodes___ = nodes;
    /*: nodes htmlElts */ "#thaw";
    this.___star___ = star && nodes.length > 1;
    /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
    star = false;
    var self = this;
    /*: self (~lBunch,frzn) */ "#freeze";
    return self;      //PV: added return
  };

  var  append = 
  /*: (this: Ref(~lBunch), appendage: Ref(lArr)) 
      / (lArr: Arr(Ref(~lBunch)) > lArrPro) -> Top / sameType */
      "#extern";
   
//  var blur = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";
//
//  var check  = 
//  /*: {(and
//      (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(NotUndef) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
//      (v :: (this: Ref(~lBunch), value: Ref) / (value: {} > lObjPro) -> Ref(~lBunch) / sameType) 
//      ) } */ "#extern";
//
//  var class_ =
//  /*: {(and
//      (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
//      (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch) ) 
//      )} */ "#extern";
//
//
//  var clone = /*: (this: Ref(~lBunch), deep:Bool, n: {Int|(>= v 0)}) -> 
//    {(ite (truthy n) (v::Ref(~lBunches)) (v::Ref(~lBunch)))} */ "#extern";
//
//  var count = /*: (this: Ref(~lBunch)) -> Int */ "#extern";
//
//  var each = /*: (this: Ref(~lBunch), func: (Ref(~lBunch)) -> Top) -> Top */ "#extern";
//
//  var empty = 
//  /*: {(and
//      (v :: (this: Ref(~lBunch)) / (&value: Ref(lArr), lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
//      (v :: (this: Ref(~lBunch)) / (&value: Ref(lObj), lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType)
//      )} */ "#extern";
//
//  var enable = 
//  /*: {(and
//      (v :: (this: Ref(~lBunch), enable: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
//      (v :: (this: Ref(~lBunch), enable: Ref(lObj)) / (lObj: { }  > lObjPro) -> Ref(~lBunch) / sameType))} */ "#extern";
//
//  var ephemeral_ = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";
//
//  var explode = /*: [;L;] (this: Ref(~lBunch)) / () -> Ref(L) / (L: Arr(Ref(~lBunch)) > lArrPro) */ "#extern";

  var fire = 
  /*: {(and
      (v :: (this: Ref(~lBunch), event: Str) -> Ref(~lBunch))
      (v :: (this: Ref(~lBunch), event: Ref(~lEvent)) -> Ref(~lBunch)))} */ "#extern";

//  var focus            = /*: (this: Ref(~lBunch)) / (&has_focus: Top) -> Top / sameType*/ "#extern";
//  var fragment         = /*: (this: Ref(~lBunch))      -> Ref(~lBunch) */ "#extern";
//  var getCheck         = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getChecks        = /*: (this: Ref(~lBunch))      -> Ref(~lChecked) */ "#extern";
//  var getClass         = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getClasses       = /*: (this: Ref(~lBunch))      -> Ref(~lClassNames) */ "#extern";
//  var getMark          = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getMarks         = /*: (this: Ref(~lBunch))      -> Ref(~lADsafeMarks) */ "#extern";
//  var getName          = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getNames         = /*: (this: Ref(~lBunch))      -> Ref(~lNames) */ "#extern";
//  var getOffsetHeight  = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getOffsetHeights = /*: (this: Ref(~lBunch))      -> Ref(~lOffsetHeights) */ "#extern";
//  var getOffsetWidth   = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getOffsetWidths  = /*: (this: Ref(~lBunch))      -> Ref(~lOffsetWidths) */ "#extern";
//  var getParent        = /*: (this: Ref(~lBunch))      -> Ref(~lBunch) */ "#extern";
//  var getSelection     = /*: (this: Ref(~lBunch))      -> {(or (Str v) (= v null))} */ "#extern";
//  var getStyle         = /*: (this: Ref(~lBunch), Str) -> Ref(~lStyle) */ "#extern";
//  var getStyles        = /*: (this: Ref(~lBunch), Str) -> Ref(~lStyles) */ "#extern";
//  var getTagName       = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getTagNames      = /*: (this: Ref(~lBunch))      -> Ref(~lNames) */ "#extern";
//  var getTitle         = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getTitles        = /*: (this: Ref(~lBunch))      -> Ref(~lNames) */ "#extern";
//  var getValue         = /*: (this: Ref(~lBunch))      -> Top */ "#extern";
//  var getValues        = /*: (this: Ref(~lBunch))      -> Ref(~lValues) */ "#extern";
// 
//  var klass = /*: (this: Ref(~lBunch), value: Str) -> Top */ "#extern";
//
//  var mark =
//  /*: {(and
//      (v :: (this: Ref(~lBunch), value: Ref(lArr)) 
//        / (lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
//      (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch)) )} */ "#extern";
//
//  var off = /*: (this: Ref(~lBunch), type_:Top) -> Ref(~lBunch) */ "#extern";
//
//  var on = /*: (this: Ref(~lBunch), type_:Top, func: (Top) -> Top) -> Ref(~lBunch) */ "#extern";
//
//  var protect = /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ "#extern";
//
//  var q = /*: (this: Ref(~lBunch), Str) -> Ref(~lBunch) */ "#extern";

  var remove = /*: (this: Ref(~lBunch)) -> Top */ "#extern";


//  var replace = /*: {(and
//        (v:: (this: Ref(~lBunch), replacement: Ref(lA)) / (lA: tyBunchArr) -> Top / sameExact )
//        (v:: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact )
//        (v:: (this: Ref(~lBunch))-> Top )
//    )} */ "#extern";
//    
//  var select = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
//
//  var selection = /*: (this: Ref(~lBunch), string: Str) -> Ref(~lBunch) */ "#extern";
//
//  var style = /*: {( and 
//      (v:: (this: Ref(~lBunch), name: Str, value: Str) -> Ref(~lBunch))
//      (v:: (this: Ref(~lBunch), name: Str, value: Ref(lA)) 
//      / (lA: {Arr(Str)|(packed v)} > lArrPro) -> Ref(~lBunch) / sameType)
//    )}*/ "#extern";
//
//  var tag = /*: (this: Ref(~lBunch), tag_: Str, type_: Str, name: Str) -> Ref(~lBunch) */ "#extern";
//
//  var text = /*: {( and 
//      (v:: (this: Ref(~lBunch), text: Str) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//      (v:: (this: Ref(~lBunch), text: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//    )}*/ "#extern";
//
//  var title = /*: {( and 
//      (v:: (this: Ref(~lBunch), value: Str) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//      (v:: (this: Ref(~lBunch), value: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//    )}*/ "#extern";
//
//  var value_ = /*: {( and 
//      (v:: (this: Ref(~lBunch), value: Str)     / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//      (v:: (this: Ref(~lBunch), value: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//    )}*/ "#extern";
//

//  PV: changed the structure considerably
//  Bunch.prototype.append = append;
//  TODO: Commenting rest of the functions to scale  
//  Bunch.prototype.blur = blur;
//  Bunch.prototype.check = check;
//  Bunch.prototype['class'] = class_;
//  Bunch.prototype.clone = clone;
//  Bunch.prototype.count = count;
//  Bunch.prototype.each = each;
//  Bunch.prototype.empty = empty;
//  Bunch.prototype.enable = enable;
//  Bunch.prototype.ephemeral_ = ephemeral_;
//  Bunch.prototype.explode = explode;
  Bunch.prototype.fire = fire;
//  Bunch.prototype.focus = focus;
//  Bunch.prototype.fragment = fragment;
//  Bunch.prototype.getCheck = getCheck; 
//  Bunch.prototype.getClass = getClass;
//  Bunch.prototype.getClasses = getClasses;
//  Bunch.prototype.getMark = getMark;
//  Bunch.prototype.getMarks = getMarks;
//  Bunch.prototype.getName = getName;
//  Bunch.prototype.getNames = getNames;
//  Bunch.prototype.getOffsetHeight = getOffsetHeight;
//  Bunch.prototype.getOffsetHeights = getOffsetHeights; 
//  Bunch.prototype.getOffsetWidth = getOffsetWidth;
//  Bunch.prototype.getOffsetWidths = getOffsetWidths;
//  Bunch.prototype.getParent = getParent;
//  Bunch.prototype.getSelection = getSelection;
//  Bunch.prototype.getStyle = getStyle;
//  Bunch.prototype.getStyles = getStyles;
//  Bunch.prototype.getTagName = getTagName;
//  Bunch.prototype.getTagNames = getTagNames;
//  Bunch.prototype.getTitle = getTitle;
//  Bunch.prototype.getTitles = getTitles;
//  Bunch.prototype.getValue = getValue;
//  Bunch.prototype.getValues = getValues;
//  Bunch.prototype.klass = klass;
//  Bunch.prototype.mark = mark;
//  Bunch.prototype.off = off;
//  Bunch.prototype.on = on;
//  Bunch.prototype.protect = protect;
//  Bunch.prototype.q = q;
//  Bunch.prototype.remove = remove;
//  Bunch.prototype.replace = replace;  //TODO
//  Bunch.prototype.select = select;
//  Bunch.prototype.selection = selection;
//  Bunch.prototype.style = style;
//  Bunch.prototype.tag = tag;
//  Bunch.prototype.text = text;
//  Bunch.prototype.title = title;
//  Bunch.prototype.value = value_;
//
  
//-------------------------------------------------------------------
// Moving the definition of dom_event after the definition of Bunch.proto
//-------------------------------------------------------------------

  var allow_focus /*: Bool */ = true,
      dom /*: Ref(~lDom) */ = null,

      dom_event = function (e) /*: (Ref(~lEvent)) -> Top */
      {
        var key /*: Str */ = "";
        var the_actual_event /*: Ref(~lEvent) */ = e || event;

        ///XXX: thawing here does a big difference in performance.
        /*: the_actual_event lEvent */ "#thaw";
        assume(the_actual_event != null);
        var type = the_actual_event.type_;
        assume(type != undefined);


        // Get the target node and wrap it in a bunch.

        var the_target = the_actual_event.target || the_actual_event.srcElement;
        /*: the_actual_event (~lEvent, thwd lEvent) */ "#freeze";

        //PV: can either keep this or change the type of event to 
        //definitely contain these fields.
        assume(the_target != undefined);

        var tt = /*: lTT {Arr(Ref(~htmlElt))|(packed v)} */ [the_target];
        /*: tt (~htmlElts, frzn) */ "#freeze";

        var target = new Bunch(tt);
        var that /*: Ref(~lBunch) */ = target;

        // Use the PPK hack to make focus bubbly on IE.
        // When a widget has focus, it can use the focus method.

//PV: Original code begin
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
//PV: Original code end


//        if (type == 'mousedown') {
//          allow_focus = true;
//          if (document.selection) {
//            the_range = document.selection.createRange();
//          }
//        }
//        else if(type == 'focus' || type == 'focusin') {
//            allow_focus = true;
//            has_focus = the_target;
////XXX: SLOW DOWN !!! ~ 11 sec            
////            /*: the_actual_event lEvent */ "#thaw";
////            the_actual_event.cancelBubble = false;
////            /*: the_actual_event (~lEvent, thwd lEvent) */ "#freeze";
//            type = 'focus';
//        }
//        else if (type == 'blur' || type == 'focusout') {
//          allow_focus = false;
//          has_focus = null;
//          type = 'blur';
//        }
//        else if (type == 'keypress') {
//          allow_focus = true;
//          has_focus = the_target;
//          //PV: original code begin
//          //key = String.fromCharCode(the_actual_event.charCode || the_actual_event.keyCode);
//          //PV: original code end
//
////XXX: SLOW DOWN !!! ~ 9 sec
////          /*: the_actual_event lEvent */ "#thaw";
////          var tmp = the_actual_event.charCode || the_actual_event.keyCode;
////          key = stringFromCharCode(tmp);
////          /*: the_actual_event (~lEvent, thwd lEvent) */ "#freeze";
//          
//          if (key == '\u000d' || key == '\u000a') {
//            type = 'enterkey';
//          }
//          else if (key == '\u001b') {
//            type = 'escapekey';
//          }
//        } 
//        // This is a workaround for Safari.
//        else if(type == 'click') {
//          allow_focus = true;
//        }


//XXX: SLOW DOWN !!! ~ 55 sec 
//        /*: the_actual_event lEvent */ "#thaw";
//        if (the_actual_event.cancelBubble &&
//            the_actual_event.stopPropagation) {
//              the_actual_event.stopPropagation();
//            }
//        /*: the_actual_event (~lEvent, thwd lEvent) */ "#freeze";

        // Make the event object.
//
//        /*: the_actual_event le */ "#thaw";
//        assume(the_actual_event != null);
//
//        var tmp_event = {
//          altKey: the_actual_event.altKey,
//          ctrlKey: the_actual_event.ctrlKey,
//          bubble: function () /*: () -> Top */
//          {
//
//      //TODO: try-catch, self-reference
//      //      // Bubble up. Get the parent of that node. It becomes the new that.
//      //      // getParent throws when bubbling is not possible.
//      //
//      //      try {
//      //        var parent = that.getParent();
//      //        b = parent.___nodes___[0];
//      //        that = parent;
//      //        the_event.that = that;
//      //  
//      //        // If that node has an event handler, fire it. Otherwise, bubble up.
//      //  
//      //        if (b['___ on ___'] &&
//      //            b['___ on ___'][type]) {
//      //              that.fire(the_event);
//      //            } else {
//      //              the_event.bubble();
//      //            }
//      //      } catch (e) {
//      //        error(e);
//      //      }
//          },
//          key: key,
//          //PV: question: what gets added in the place of ~lEvent if we do not specify
//          //it ??
//          preventDefault: function () /*: () / (~lEvent:frzn) -> Top / sameType */
//          {
//            /*: the_actual_event le1 */ "#thaw";
//            assume(the_actual_event != null);
//            if (the_actual_event.preventDefault) {
//              the_actual_event.preventDefault();
//            }
//            the_actual_event.returnValue = false;
//            /*: the_actual_event (~lEvent, thwd le1) */ "#freeze";
//          },
//          shiftKey: the_actual_event.shiftKey,
////XXX Cannot TC because target and that should be htmlElements but get assigned 
////Bunches instead
////          target: target,
////          that: that,
//          type: type,
//          x: the_actual_event.clientX,
//          y: the_actual_event.clientY
//        };
//
//        /*: the_actual_event (~lEvent, thwd le) */ "#freeze";
//
//        /*: tmp_event (~lEvent, frzn) */ "#freeze";
//        the_event = tmp_event;

        
        // if the target has event handlers, then fire them. otherwise, bubble up.

        /*: the_target elt1 */ "#thaw";
        assume(the_target != null);
        assert(/*: Ref(~lEvent) */ (the_event));
        /*: the_event ev1 */ "#thaw";
        assume(the_event != null);
            
        if (the_target['___ on ___'] 
//TODO            
//            the_target['___ on ___'][the_event.type_])  //PV: original code - not TCing 
//            the_target['___ on ___']["a"]
              ) 
        {
          target.fire(the_event);
        } 
        /*: the_event (~lEvent, thwd ev1) */ "#freeze";
        /*: the_target (~htmlElt, thwd elt1) */ "#freeze";
//        else {
//          var brk /*: Bool */ = false;
//          for (;!brk;) {
//            the_target = the_target.parentNode;
//            if (!the_target) {
//              brk = true;             //PV: replaced break with this
//            }
//            else if (the_target['___ on ___'] &&
////TODO                
////                the_target['___ on ___'][the_event.type]) 
//                the_target['___ on ___']["a"]) 
//            {
//              var tt1 = /*: lTT Arr(Ref(~htmlElt)) */ [the_target];
//              /*: tt1 (~htmlElts, frzn) */ "#freeze";
//              that = new Bunch(tt1);
//              /*: the_event lEvent */ "#thaw";
//              the_event.that = that;
//              that.fire(the_event);
//              /*: the_event (~lEvent, thwd lEvent) */ "#freeze";
//              brk = true;             //PV: replaced break with this
//            }
//            else if (the_target['___adsafe root___']) {
//              brk = true;             //PV: replaced break with this
//            }
//          }
//        };
//        if (the_event.type_ === 'escapekey') {
//          if (ephemeral) {
//            ephemeral.remove();
//          }
//          ephemeral = null;
//        }
//        that = the_target = the_event = the_actual_event = null;
//
//        return;
      };

      // Mark the node as a root. This prevents event bubbling from propagating
      // past it.

//      root['___adsafe root___'] = '___adsafe root___';



//-------------------------------------------------------------------
//    Dom object definitions
//-------------------------------------------------------------------

//      var dom_append = /*: (Ref(~lBunch)) -> Ref(~lDom) */ "#extern"; 
//
//      var dom_combine = /*: (Ref(~lBunches)) -> Ref(~lBunch) */ "#extern";
//
//      var dom_count = /*: () -> Int */ "#extern";
//
//      var dom_ephemeral = /*: (Ref(~lBunch)) -> Ref(~lDom) */ "#extern";
//
//      var dom_fragment = /*: () -> Ref(~lBunch) */ "#extern";
//
//      var dom_prepend = /*: (Ref(~lBunch)) -> Ref(~lDom) */ "#extern";
//
//      var dom_q = 
//        /*: [;L;] (text: Str) /  ( &hunter: Ref(L), L: {
//          empty_  : (Ref(~htmlElt)) -> Top ,
//          plus    : (Ref(~htmlElt)) -> Top ,
//          greater : (Ref(~htmlElt)) -> Top ,
//          pound   : (Ref(~htmlElt)) -> Top ,
//          slash   : (Ref(~htmlElt)) -> Top ,
//          star    : (Ref(~htmlElt)) -> Top ,
//          _       : Bot
//          } > lObjPro)  
//          -> Ref(~lBunch) / sameType */ "#extern";
//
//        var dom_remove = /*: () -> Top */ "#extern";
//
//      var dom_row = /*: (values: Ref(~htmlElts)) -> Ref(~lBunch) */ "#extern";
//
//      var dom_tag = /*: (tag_: Str, type_: Str, name: Str) -> Ref(~lBunch) */ "#extern";
//
//      var dom_text =
//        /*: {( and
//          (v:: (text: Str) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//          (v:: (text: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//          )}*/ "#extern";
//
//        // Return an ADsafe dom object.
//
//        dom = {
//          append: dom_append,
//          combine: dom_combine,
//          count: dom_count, 
//          ephemeral: dom_ephemeral,
//          fragment: dom_fragment,
//          prepend: dom_prepend,
//          q: dom_q,
//          remove: dom_remove,
//          row: dom_row,
//          tag: dom_tag,
//          text: dom_text
//        };
//
//
      if (typeof root.addEventListener === 'function') {
//TODO: Need to fix function subtyping
        // root.addEventListener('focus', dom_event, true);
        // root.addEventListener('blur', dom_event, true);
        // root.addEventListener('mouseover', dom_event, true);
        // root.addEventListener('mouseout', dom_event, true);
        // root.addEventListener('mouseup', dom_event, true);
        // root.addEventListener('mousedown', dom_event, true);
        // root.addEventListener('mousemove', dom_event, true);
        // root.addEventListener('click', dom_event, true);
        // root.addEventListener('dblclick', dom_event, true);
        // root.addEventListener('keypress', dom_event, true);
      } else {
        // root.onfocusin       = root.onfocusout  = root.onmouseout  =
        // root.onmousedown = root.onmousemove = root.onmouseup   =
        // root.onmouseover = root.onclick     = root.ondblclick  =
        // root.onkeypress  = dom_event;
      }



//      return /*: L {Arr(Top)|(and  (packed v)  (= (len v) 2)  ({(v::Ref(~lDom))} (sel v 0))   ({(v::Ref(lBunchProto))} (sel v 1))) } */ [dom, Bunch.prototype];
//      return [dom, Bunch.prototype];
};
