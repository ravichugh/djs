
var int_to_string /*: (Int) -> Str */ = "#extern";
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

//XXX: replace all "newBunch" with "newBunch"
var newBunch = /*: (Ref(~htmlElts)) -> Ref(~lBunch) */ "#extern";

var assumeArray   = /*: ()-> Ref(~en) */ "#extern";
var assumeBool    = /*: ()-> Bool     */ "#extern";

var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";


/*: tyArr {Arr(Ref(~htmlElt))|(packed v)} > lArrPro */ "#define";

var ephemeral /*: Ref(~lBunch) */ = "#extern";
var star    /*: Bool */         = "#extern";

// A Bunch is a container that holds zero or more dom nodes.
// It has many useful methods.

function Bunch(nodes)
  /*: new (this:Ref, nodes: Ref(~htmlElts)) / (this: Empty > lBunchProto, ~lBunch: frzn) ->
    Ref(~lBunch) / (~lBunch: frzn) */
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

var remove = /*: (this: Ref(~lBunch)) -> Top */ "#extern";
Bunch.prototype.remove = remove;

var reject_global = /*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

// -----------------------------------------------------------------------------------

/*: (~en: {Arr(Bool)|(packed v)} > lArrPro) */ "#weak";

var enable = function (enable) 
/*: {(and 
        (v::(this: Ref(~lBunch), enable: Ref(~en)) -> Ref(~lBunch))  
        (v::(this: Ref(~lBunch), enable: Bool) -> Ref(~lBunch))
    )} */
{
  reject_global(this);
 
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0,
      node /*: Ref(~htmlElt) */ = null;
  
  var tmp_bl;

  if (isArray(enable)) {
    enable = assumeArray();
    /*: enable lEnable */ "#thaw";
    assume(enable != null);
    /*: b htmlElts */ "#thaw";
    tmp_bl = b.length;
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    if (enable.length !== tmp_bl) {
      //error('ADsafe: Array length: ... ' );
      error('ADsafe: Array length: ' + int_to_string(tmp_bl) + '-' +
          int_to_string(enable.length));
    }
    
    /*: b htmlElts */ "#thaw";
    assume(b != null);
    /*: ( &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro,
          &enable: Ref(lEnable), lEnable: {Arr(Bool)|(packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      assume(node != null);
      if (node.tagName) {
        node.disabled = !enable[i];
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    /*: enable (~en, thwd lEnable) */ "#freeze";
  } 
  else {
    enable = assumeBool();
    /*: b htmlElts */ "#thaw";
    assume(b != null);
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameExact */
    for (i = 0; i < b.length; i += 1) {      
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagName) {
        node.disabled = !enable;
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  return this;
};

var ephemeral_ = function () 
/*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  reject_global(this);
  if (ephemeral) {
    ephemeral.remove();
  }
  ephemeral = this;
  return this;
};



var explode = function () 
/*: [;L;] (this: Ref(~lBunch)) / () -> Ref(L) / (L: Arr(Ref(~lBunch)) > lArrPro) */
{
  reject_global(this);
  var a = /*: L {Arr(Ref(~lBunch))|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0;

  /*: (&b: Ref(~htmlElts), &a: Ref(L), L: Arr(Ref(~lBunch)) > lArrPro) -> sameType */
  for (i = 0; true; i += 1) {
    /*: b htmlElts */ "#thaw";
    if (i < b.length) {
      var bArr = /*: lBArr {Arr(Ref(~htmlElt))|(packed v)} */  [b[i]];
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
      /*: bArr (~htmlElts, frzn) */ "#freeze";
      a[i] =  newBunch(bArr);
    }
    else{
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    }
  }
  return a;
};

