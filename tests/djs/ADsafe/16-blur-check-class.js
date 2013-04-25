var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
var intToString = /*: (Int) -> Str */ "#extern";
 


/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var reject_global = 
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */ "#extern";

var star /*: Bool */ = "#extern";

var blur = function () /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  /*: this lBunch */ "#thaw";
  assume(this != null);
  reject_global(this);
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var i /*: {Int | (>= v 0)}*/ = 0,
      node /*: Ref(~htmlElt) */ = null,       
      has_focus /*: Ref(~htmlElt) */ = null;

  /*: b htmlElts */ "#thaw";
  b.l;
  /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    if (node.blur) {
      node.blur();
    }
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

  return this;
};


//Q: why does it not work with value: Ref(lArr?)
var check  = function (value)
/*: {(and
    (v :: (this: Ref(~lBunch), value: Ref) / (value: { Arr(NotUndef) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), value: Ref) / (value: {} > lObjPro) -> Ref(~lBunch) / sameType)
    )} */
{
  //reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  var i /*: {Int | (>= v 0)} */ = 0,
      node /*: Ref(~htmlElt) */ = null;
  if (isArray(value)) {
    /*: b htmlElts */ "#thaw";
    if (value.length !== b.length) {
      //PV: added calls to intToString
      error('ADsafe: Array length: ' + intToString(b.length) + '-' + intToString(value.length));
    }
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagName) {
        node.checked = !!value[i];
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  else {
    /*: b htmlElts */ "#thaw";
    b.length;
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      if (node.tagName) {
        node.checked = !!value;
      }
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  return this;
};


var class_fun = function (value) 
/*: {(and
    (v :: (this: Ref(~lBunch), value: Ref) / (value: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch) )
    )} */
{
  //reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___; 
  var i /*: {Int | (>= v 0)} */ = 0,
      node /*: Ref(~htmlElt) */ = null;
  if (isArray(value)) {
    /*: b htmlElts */ "#thaw";
    if (value.length !== b.length) {
    //  error('ADsafe: Array length: ' + b.length + '-' +
    //       value.length);
    }
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
//      //TODO: RegEx support needed      
//      if (/url/i.test(string_check(value[i]))) {
//        error('ADsafe error.');
//      }
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagName) {
        if (value[i])     //XXX: Would be cool if I didn't have to add this
        node.className = value[i];
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  else {
//    //TODO: RegEx support needed      
//    if (/url/i.test(string_check(value))) {
//      error('ADsafe error.');
//    }
    /*: b htmlElts */ "#thaw";
    b.l;
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagName) {
        node.className = value;
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  return this;
};
