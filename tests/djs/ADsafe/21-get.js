/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var allow_focus /*: Bool */ = "#extern";
var star    /*: Bool */         = "#extern";
var the_range /*: Ref(~lRange) */  = "#extern";

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

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var reject_name = /*: (Str) -> Bool */ "#extern";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var getStyleObject = /*: (node: Ref(~lNode)) -> Ref(~lStyle) */ "#extern";

// -----------------------------------------------------------------------------------


Bunch.prototype.getChecks = function () /*: (this: Ref(~lBunch)) -> Ref(~lChecked) */ {
  reject_global(this);
  var a = /*: lA {Arr(Bool)|(packed v)} */ [];
  var b = this.___nodes___;
  var i = 0;

  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Bool)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: {Arr(Bool)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i].checked;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lChecked, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getClasses =  function () /*: (this: Ref(~lBunch)) -> Ref(~lClassNames) */ {
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;

  /*: b lNodes */ "#thaw";
  b.l;

  /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Str)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: {Arr(Str)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i].className;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lClassNames, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getMarks = function () /*: (this: Ref(~lBunch)) -> Ref(~lADsafeMarks) */ {
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;

  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Str)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: {Arr(Str)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i]['_adsafe mark_'];
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lADsafeMarks, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getNames = function () /*: (this: Ref(~lBunch)) -> Ref(~lNames) */ {
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Str)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: {Arr(Str)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i].name;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lNames, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getOffsetHeights = function () /*: (this: Ref(~lBunch)) -> Ref(~lOffsetHeights) */ {
  reject_global(this);
  var a = /*: lN {Arr(Num)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lN:{Arr(Num)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lN: {Arr(Num)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i].offsetHeight;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lOffsetHeights, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getOffsetWidths = function () /*: (this: Ref(~lBunch)) -> Ref(~lOffsetWidths) */ {
  reject_global(this);
  var a = /*: lN {Arr(Num)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lN:{Arr(Num)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lN: {Arr(Num)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i].offsetWidth;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lOffsetWidths, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getStyles = function (name) /*: (this: Ref(~lBunch), Str) -> Ref(~lStyles) */ {
  reject_global(this);
  if (reject_name(name)) {
    error("ADsafe style violation.");
  }
  var a = /*: lA Arr(Str) */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  var node /*: Ref(~lNode) */ = null , s;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lA:Arr(Str)  > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro, &s: Top)
      -> ( &i: sameType, lA: Arr(Str) > lArrPro, &b: sameType, lNodes: sameType, &s: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    if (node.tagName) {
      s = name !== 'float'
        ? getStyleObject(node)[name]
        : getStyleObject(node).cssFloat ||
        getStyleObject(node).styleFloat;
      if (typeof s === 'string') {
        a[i] = s;
      }
    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lStyles, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getTagNames = function () /*: (this: Ref(~lBunch)) -> Ref(~lNames) */ {
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  var name /*: Str */ = "";
  /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Str)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: {Arr(Str)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    name = b[i].tagName;
    a[i] = typeof name === 'string' ? name.toLowerCase() : name;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lNames, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getTitles = function () /*: (this: Ref(~lBunch)) -> Ref(~lNames) */ {
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Str)|(and (packed v) (= (len v) i0))} > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: {Arr(Str)|(packed v)} > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    a[i] = b[i].title;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lNames, frzn) */ "#freeze";
  return a;
};

Bunch.prototype.getValues = function () /*: (this: Ref(~lBunch)) -> Ref(~lValues) */ {
  reject_global(this);
  var a = /*: lA Arr(Str) */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  var node /*: Ref(~lNode) */ = null;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)}, lA:Arr(Str)  > lArrPro,
        &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
      -> ( &i: sameType, lA: Arr(Str) > lArrPro, &b: sameType, lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    if (node.nodeName === '#text') {
      a[i] = node.nodeValue;
    } else if (node.tagName && node.type !== 'password') {
      a[i] = node.value;
      if (!a[i] && node.firstChild &&
          node.firstChild.nodeName === '#text') {
            a[i] = node.firstChild.nodeValue;
          }
    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lValues, frzn) */ "#freeze";
  return a;
};

var getCheck = function () /*: (this: Ref(~lBunch)) -> {?(Bool)|TRU} */ {
//  return this.getChecks()[0];   //PV: original code
  var elts = this.getChecks();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lChecked, thwd lElts) */ "#freeze";
  return ret;
};

var getClass = function () /*: (this: Ref(~lBunch)) ->  {?(Str)|TRU} */ {
//  return this.getClasses()[0]; //PV: original code
  var elts = this.getClasses();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lClassNames, thwd lElts) */ "#freeze";
  return ret;
};

var getMark = function () /*: (this: Ref(~lBunch)) -> {?(Str)|TRU} */ {
//  return this.getMarks()[0];    //PV: o.c.
  var elts = this.getMarks();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lADsafeMarks, thwd lElts) */ "#freeze";
  return ret;
};

var getName = function () /*: (this: Ref(~lBunch)) -> {?(Str)|TRU} */ {
//return this.getNames()[0];    //PV: o.c.
  var names = this.getNames();
  /*: names lNames */ "#thaw";
  var ret = names[0];
  /*: names (~lNames, thwd lNames) */ "#freeze";
  return ret;
};

var getOffsetHeight = function () /*: (this: Ref(~lBunch)) -> {?(Num)|TRU} */ {
//  return this.getOffsetHeights()[0];
  var elts = this.getOffsetHeights();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lOffsetHeights, thwd lElts) */ "#freeze";
  return ret;
};

var getOffsetWidth = function () /*: (this: Ref(~lBunch)) -> {?(Num)|TRU} */ {
//  return this.getOffsetWidths()[0];
  var elts = this.getOffsetWidths();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lOffsetWidths, thwd lElts) */ "#freeze";
  return ret;
};

var getParent = function () /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */ {
  reject_global(this);
  var a = /*: lA {Arr(Ref(~lNode))|(packed v)} */ [];
  var b = this.___nodes___;
  var i /*: { Int | (>= v 0)} */ = 0;
  var n /*: Ref(~lNode) */ = null;
  /*: b lNodes */ "#thaw";
  b.l;
  /*: ( &i:i0:{Int|(>= v 0)},  &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro, 
        lA:{Arr(Ref(~lNode))|(and (packed v) (= (len v) i0))} > lArrPro)
      -> (&i: sameType, &b: sameType, lA: {Arr(Ref(~lNode))|(packed v)} > lArrPro,lNodes: sameType) */ 
  for (i = 0; i < b.length; i += 1) {
    n = b[i].parentNode;
    if (n['___adsafe root___']) {
      error('ADsafe parent violation.');
    }
    a[i] = n;
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  /*: a (~lNodes, frzn) */ "#freeze";
  return new Bunch(a);
};


var getSelection = function () 
/*: (this: Ref(~lBunch)) -> {(or (Str v) (= v null))} */
{
  reject_global(this);
  var b = this.___nodes___;
  var end, node, start, range;
  var str;  //PV 
  /*: b lNodes */ "#thaw";
  if (b.length === 1 && allow_focus) {
    node = b[0];
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
    if (typeof node.selectionStart === 'number') {
      start = node.selectionStart;
      end = node.selectionEnd;
      str = node.value;
      return str.slice(start, end);
    }
    else {
      range = node.createTextRange();
      range.expand('textedit');
      if (range.inRange(the_range)) {
        return the_range.text;
      }
      else {
        return null;
      }
    }
  }
  else {
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  return null;
};

var getStyle = function (name) /*: (this: Ref(~lBunch), Str) -> {?(Str)|TRU} */ {
//  return this.getStyles(name)[0];   //PV: o.c.
  var elts = this.getStyles(name);
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lStyles, thwd lElts) */ "#freeze";
  return ret;
};

var getTagName = function () /*: (this: Ref(~lBunch)) -> {?(Str)|TRU} */ {
//  return this.getTagNames()[0];   //PV: o.c.
  var elts = this.getTagNames();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lNames, thwd lElts) */ "#freeze";
  return ret;
};

var getTitle = function () /*: (this: Ref(~lBunch)) -> {?(Str)|TRU} */ {
//  return this.getTitles()[0];
  var elts = this.getTitles();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lNames, thwd lElts) */ "#freeze";
  return ret;
};

var getValue = function () /*: (this: Ref(~lBunch)) -> {?(Str)|TRU} */ {
//  return this.getValues()[0];
  var elts = this.getValues();
  /*: elts lElts */ "#thaw";
  var ret = elts[0];
  /*: elts (~lValues, thwd lElts) */ "#freeze";
  return ret;
};

