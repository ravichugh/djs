/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document  /*: Ref(~lDocument) */ = "#extern";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var int_to_string /*: (Int) -> Str */ = "#extern";


var makeableTagName = {

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



var tag = function (tag_, type_, name) 
/* (this: Ref(~lBunch), tag_: Str, type_: Str, name: Str)-> Ref(~lBunch)  */
/*: (this: Ref(~lBunch), tag_: Str, type_: Str, name: Str)-> Top */
{
  reject_global(this);
  var node /*: Ref(~lNode) */ = null;
  if (typeof tag_ !== 'string') {
    error("default");   //PV: adding arg
  }
  if (makeableTagName[tag_] !== true) {
    error('ADsafe: Bad tag: ' + tag_);
  }
  node = document.createElement(tag_);
  if (name) {
//TODO: slowdown    
    node.autocomplete = 'off';
    node.name = string_check(name);
  }
  if (type_) {
    node.type = string_check(type_);
  }
  //var nodeArg = /*: lN {Arr(Ref(~lNode))|(packed v)} */ [node];
  ///*: nodeArg (~lNodes,frzn) */ "#freeze";
  //return new Bunch(nodeArg);
};

//var text = function (text) 
///*: {( and 
//    (v:: (this: Ref(~lBunch), text: Str) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//    (v:: (this: Ref(~lBunch), text: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//)}*/
//{
//  reject_global(this);
//  var a, i;
//  if (isArray(text)) {
//    a = /*: lA {Arr(Ref(~lNode))|(packed v)} */ [];
//    /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Ref(~lNode))|(and (packed v) (= (len v) i0))} > lArrPro,
//          &text: Ref(lT), lT: {Arr(Str)|(packed v)} > lArrPro)
//        -> ( &i: sameType, lA: {Arr(Ref(~lNode))|(packed v)} > lArrPro, &text: sameType, lT: sameType) */ 
//    for (i = 0; i < text.length; i += 1) {
//      a[i] = document.createTextNode(string_check(text[i]));
//    }
//    /*: a (~lNodes, frzn) */ "#freeze";
//    return new Bunch(a);
//  }
//  else {  //PV: added else
//    var arg = /*: lArg {Arr(Ref(~lNode))|(packed v)} */ [document.createTextNode(string_check(text))];
//    /*: arg (~lNodes, frzn) */ "#freeze";
//    return new Bunch(arg);
//  }
//};
//
//var title = function (value) 
///*: {( and 
//    (v:: (this: Ref(~lBunch), value: Str) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//    (v:: (this: Ref(~lBunch), value: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
//)}*/
//{
//  reject_global(this);
//  var b = this.___nodes___, i /*: {Int|(>= v 0)} */ = 0, node /*: Ref(~lNode) */ = null;
//  if (isArray(value)) {
//    /*: b lNodes */ "#thaw";
//    b.l;
//    if (value.length !== b.length) {
////TODO: Exp frozen state      
////      error('ADsafe: Array length: ' + int_to_string(b.length) +
////          '-' + int_to_string(value.length));
//    }
//    /*: ( &value: Ref(lT), lT:{Arr(Str)|(packed v)} > lArrPro,
//          &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
//        -> ( &value: sameType, lT: sameType, &b: sameType, lNodes: sameType) */ 
//    for (i = 0; i < b.length && i > value.length; i += 1) { //PV: Added value.length
//      node = b[i];
//      var val = value[i];
//      if (node.tagName) {
//        node.title = string_check(val);
//      }
//    }
//    /*: b (~lNodes, thwd lNodes) */ "#freeze";
//  }
//  else {
//    string_check(value);
//    /*: b lNodes */ "#thaw";
//    b.l;
//    /*: ( &b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(packed v)} > lArrPro)
//        -> ( &b: sameType, lNodes: sameType) */ 
//    for (i = 0; i < b.length; i += 1) {
//      node = b[i];
//      if (node.tagName) {
//        node.title = value;
//      }
//    }
//    /*: b (~lNodes, thwd lNodes) */ "#freeze";
//  }
//  return this;
//};
//
