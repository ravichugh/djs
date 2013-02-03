/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";
var star  /*: Bool */               = "#extern";

var blur = function () /*: (this: Ref(~lBunch)) -> Ref(~lBunch) */
{
  //TODO: TC reject_global
  //reject_global(this);
  
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var i /*: {Int | (>= v 0)}*/ = 0,
      node /*: Ref(~lNode) */ = null,       
      has_focus /*: Ref(~lNode) */ = null;

  /*: b lNodes */ "#thaw";
  b.length;         //XXX: WHY??????

  /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    node = b[i];
    if (node.blur) {
      node.blur();
    }
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";

  return this;
};


//Q: why does it not work with value: Ref(lArr?)
var check  = function (value)
/*: {(and
    (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(NotUndef) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), value: Ref) / (value: {} > lObjPro) -> Ref(~lBunch) / sameType)
    )} */
{
  //reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  var i /*: {Int | (>= v 0)} */ = 0,
      node /*: Ref(~lNode) */ = null;
  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    if (value.length !== b.length) {
      //TODO: expect frozen states
      //error('ADsafe: Array length: ' + b.length + '-' +
      //    value.length);
    }
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        node.checked = !!value[i];
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  else {
    /*: b lNodes */ "#thaw";
    b.length;
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      if (node.tagName) {
        node.checked = !!value;
      }
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  return this;
};


var class_fun = function (value) 
/*: {(and
    (v :: (this: Ref(~lBunch), value: Ref(lArr)) / (lArr: { Arr(Str) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), value: Str) -> Ref(~lBunch) )
    )} */
{
  //reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___; 
  var i /*: {Int | (>= v 0)} */ = 0,
      node /*: Ref(~lNode) */ = null;
  if (isArray(value)) {
    /*: b lNodes */ "#thaw";
    if (value.length !== b.length) {
    //  error('ADsafe: Array length: ' + b.length + '-' +
    //       value.length);
    }
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
//      //TODO: RegEx support needed      
//      if (/url/i.test(string_check(value[i]))) {
//        error('ADsafe error.');
//      }
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        if (value[i])     //XXX: Would be cool if I didn't have to add this
        node.className = value[i];
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  else {
//    //TODO: RegEx support needed      
//    if (/url/i.test(string_check(value))) {
//      error('ADsafe error.');
//    }
    /*: b lNodes */ "#thaw";
    b.length;        //XXX: WHY?????? 
    /*: (&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node lNode */ "#thaw";
      if (node.tagName) {
        node.className = value;
      }
      /*: node (~lNode, thwd lNode) */ "#freeze";
    }
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
  }
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  return this;
};
