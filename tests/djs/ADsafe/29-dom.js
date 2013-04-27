/*: "tests/djs/ADsafe/__dom.dref" */ "#use";


//TODO: replace all "newBunch" with "newBunch"
var newBunch = /*: (Ref(~htmlElts)) -> Ref(~lBunch) */ "#extern";

var document  = /*: Ref(~lDocument) */ "#extern";

var String =  /*: (Top) -> Str */ "#extern";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var root /*: Ref(~htmlElt) */ = null;

var dom = /*: Ref(~lDom) */ "#extern";

var star    /*: Bool */         = "#extern";

var id    /*: Str */         = "#extern";

var the_range /*: Ref(~lRange) */  = "#extern";

var ephemeral_ /*: Ref(~lBunch) */ = "#extern";

var parse_query = /*: (text: Str, id: Str) -> Ref(~lQuery) */ "#extern";

var quest = /*: (Ref(~lQuery), Ref(~htmlElts)) -> Ref(~htmlElts) */ "#extern";

var selector_to_string = /*: (Ref(~lSelector)) -> Str */ "#extern";

var purge_event_handlers = /*: (node: Ref(~htmlElt)) -> Top */ "#extern";

//XXX: might become more general after abstraction over weak locations
var arrayConcat = /*: (a: Ref(~htmlElts), b: Ref(~htmlElts)) -> Ref(~htmlElts) */  "#extern";

var hunter =  "#extern";

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

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


////TODO: include when including newBunch
//function Bunch(nodes)
//  /*: new (this:Ref, nodes: Ref(~htmlElts)) / (this: Empty > lBunchProto, ~lBunch: frzn) ->
//    Ref(~lBunch) / (~lBunch: frzn) */
//{
//  this.___nodes___ = nodes;
//  /*: nodes htmlElts */ "#thaw";
//  this.___star___ = star && nodes.length > 1;
//  /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//  star = false;
//  var self = this;
//  /*: self (~lBunch,frzn) */ "#freeze";
//  return self;      //PV: added return
//};



var append = function (bunch) 
  /*: (Ref(~lBunch)) -> Ref(~lDom) */ 
{
  var b = bunch.___nodes___, i /*: {Int|(>= v 0)} */ = 0, n /*: Ref(~htmlElt) */ = null;
  /*: b htmlElts */ "#thaw";
  b.l;
  /*: ( &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) -> sameType */ 
  for (i = 0; i < b.length; i += 1) {
    n = b[i];
    if (typeof n === 'string' || typeof n === 'number') {
      n = document.createTextNode(String(n));
    }
    root.appendChild(n);
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return dom;
};

var combine =  function (array) 
/*: (Ref(~lBunches)) -> Ref(~lBunch) */
{
  /*: array lBunches */ "#thaw";
  if (!array || !array.length) {
    error('ADsafe: Bad combination.');
    /*: array (~lBunches, thwd lBunches) */ "#freeze";
  }
  else {
    var bch = array[0];
    var b /*: Ref(~htmlElts) */ = bch.___nodes___, i /*: {Int|(>= v 0)} */ = 0;

    /*: ( &bch: Ref(~lBunch),
          &array: Ref(lBunches), lBunches: {Arr(Ref(~lBunch))|(packed v)} > lArrPro) -> sameType */
    for (i = 0; i < array.length; i += 1) {
//PV: original code begin
//      b = b.concat(array[i].___nodes___);
//PV: original code end
      b = arrayConcat(b, array[i].___nodes___);
    }
    /*: array (~lBunches, thwd lBunches) */ "#freeze";
    return newBunch(b);
  }
};

var count = function ()
/*: () -> Int */
{
  return 1;
};

var ephemeral = function (bunch) 
/*: (Ref(~lBunch)) -> Ref(~lDom) */
{
  if (ephemeral_) {
    //TODO: add after TCing Bunch.prototype
    //ephemeral_.remove();
  }
  ephemeral_ = bunch;
  return dom;
};

var fragment = function () 
/*: () -> Ref(~lBunch) */
{
  var a = /*: lA {Arr(Ref(~htmlElt))|(packed v)} */ [document.createDocumentFragment()];
  /*: a (~htmlElts, frzn) */ "#freeze";
  return newBunch(a);
};

var prepend = function (bunch) 
/*: (Ref(~lBunch)) -> Ref(~lDom) */
{
  var b = bunch.___nodes___, i /*: {Int|(>= v 0)} */ = 0;
  /*: b htmlElts */ "#thaw";
  b.l;
  /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    root.insertBefore(b[i], root.firstChild);
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return dom;
};

//
//var q = function (text) 
///*: [;L] (text: Str) / (&hunter: Ref(L), L: Dict > lObjPro) -> Top / sameType */
//
//{
//  star = false;
//  var query = parse_query(text, id);
//  /*: query lQuery */ "#thaw";
//  var s = query[0];
//  assume(s != undefined);
//  assume(s.op != undefined);
//
//  if (typeof hunter[s.op] !== 'function') {
//    error('ADsafe: Bad query: ' + selector_to_string(query[0]));  //PV: added conversion to string
//  }
//
//  /*: query (~lQuery, thwd lQuery) */ "#freeze";
//
//  var r =  /*: lR {Arr(Ref(~htmlElt))|(packed v)} */ [root];
//  /*: r (~htmlElts, frzn) */ "#freeze";
//  return newBunch(quest(query, r));
//};
//

var remove = function () 
/*: () -> Top */
{
  purge_event_handlers(root);
  root.parent.removeElement(root);
  root = null;
};

var row = function (values) 
/*: (values: Ref(~htmlElts)) -> Ref(~lBunch) */
{
  var tr = document.createElement('tr'),
      td /*: Ref(~htmlElt) */ = null,
      i /*: {Int|(>= v 0)} */ = 0;
  /*: values htmlElts */ "#thaw";
  values.l;
  /*: ( &values: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
      -> sameType */ 
  for (i = 0; i < values.length; i += 1) {
    td = document.createElement('td');
    td.appendChild(document.createTextNode(String(values[i])));
    tr.appendChild(td);
  }
  /*: values (~htmlElts, thwd htmlElts) */ "#freeze";
  var trArr = /*: lTr {Arr(Ref(~htmlElt))|(packed v)} */ [tr];
  /*: trArr (~htmlElts, frzn) */ "#freeze";
  return newBunch(trArr);
};

var tag = function (tag_, type_, name) 
/*: (tag_: Str, type_: Str, name: Str) -> Ref(~lBunch) */
{
  var node;
  if (typeof tag_ !== 'string') {
    error("default");   //PV: adding default message
  }
  if (makeableTagName[tag_] !== true) {
    error('ADsafe: Bad tag: ' + tag_);
  }
  node = document.createElement(tag_);
  if (name) {
    node.autocomplete = 'off';
    node.name = name;
  }
  if (type_) {
    node.type = type_;
  }
  var nodeArg = /*: lN {Arr(Ref(~htmlElt))|(packed v)} */ [node];
  /*: nodeArg (~htmlElts,frzn) */ "#freeze";
  return newBunch(nodeArg);
};

var text = function (text) 
/*: {( and
    (v:: (text: Str) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
    (v:: (text: Ref(lT)) / (lT: {Arr(Str)|(packed v)} > lArrPro) -> Top / sameType)
)}*/
{
  var a, i;
  if (isArray(text)) {
    a = /*: lA {Arr(Ref(~htmlElt))|(packed v)} */ [];
    /*: ( &i:i0:{Int|(>= v 0)}, lA:{Arr(Ref(~htmlElt))|(and (packed v) (= (len v) i0))} > lArrPro,
          &text: Ref(lT), lT: {Arr(Str)|(packed v)} > lArrPro)
        -> ( &i: sameType, lA: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro, &text: sameType, lT: sameType) */ 
    for (i = 0; i < text.length; i += 1) {
      a[i] = document.createTextNode(string_check(text[i]));
    }
    /*: a (~htmlElts, frzn) */ "#freeze";
    return newBunch(a);
  }
  else {    //PV added this
    var arg = /*: lArg {Arr(Ref(~htmlElt))|(packed v)} */ [document.createTextNode(string_check(text))];
    /*: arg (~htmlElts, frzn) */ "#freeze";
    return newBunch(arg);
  }
};
