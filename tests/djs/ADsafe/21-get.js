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

var getStyleObject = /*: (node: Ref(~lNode)) -> Ref(~lCCSStyle) */ "#extern";


//TODO
var getCheck = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getChecks()[0];
};

var getChecks = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lChecked) */
{
  reject_global(this);
  var a = /*: lA {Arr(Bool)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO
var getClass = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getClasses()[0];
};

var getClasses =  function () 
/*: (this: Ref(~lBunch)) -> Ref(~lClassNames) */
{
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO:
var getMark = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getMarks()[0];
};

var getMarks = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lADsafeMarks) */
{
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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


//TODO:
var getName = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getNames()[0];
};

var getNames = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lNames) */
{
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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


//TODO:
var getOffsetHeight = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getOffsetHeights()[0];
};

var getOffsetHeights = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lOffsetHeights) */
{
  reject_global(this);
  var a = /*: lN {Arr(Num)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO:
var getOffsetWidth = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getOffsetWidths()[0];
};

var getOffsetWidths = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lOffsetWidths) */
{
  reject_global(this);
  var a = /*: lN {Arr(Num)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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


var getParent = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  reject_global(this);
  var a = /*: lA {Arr(Ref(~lNode))|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO
var getStyle = function (name) 
/*: (this: Ref(~lBunch), Str) -> Top */
{
//  return this.getStyles(name)[0];
};

var getStyles = function (name) 
/*: (this: Ref(~lBunch), Str) -> Ref(~lStyles) */
{
  reject_global(this);
  if (reject_name(name)) {
    error("ADsafe style violation.");
  }

  var a = /*: lA Arr(Str) */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO
var getTagName = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getTagNames()[0];
};

var getTagNames = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lNames) */
{
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO
var getTitle = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getTitles()[0];
};

var getTitles = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lNames) */
{
  reject_global(this);
  var a = /*: lA {Arr(Str)|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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

//TODO
var getValue = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
//  return this.getValues()[0];
};

var getValues = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lValues) */
{
  reject_global(this);
  var a = /*: lA Arr(Str) */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
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
