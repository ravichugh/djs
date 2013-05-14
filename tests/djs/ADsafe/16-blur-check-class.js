var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
var intToString = /*: (Int) -> Str */ "#extern";
 
var assumeArray = /*: () -> Ref(~lNames!) */ "#extern";
var assumePackedValues = /*: () -> Ref(~lPackedValues!) */ "#extern";
var int_to_string /*: (Int) -> Str */ = "#extern";


/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var reject_global = 
/*: {(and (v:: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact)
    (v:: (Top) -> Top) )}  */ "#extern";

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


var check  = function (value)
/*: {(and
    (v :: (this: Ref(~lBunch!), value: Ref(~lPackedValues!)) -> Ref(~lBunch))
    (v :: (this: Ref(~lBunch!), value: Str) -> Ref(~lBunch))
    )} */
{
  reject_global(this);
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  var i /*: {Int | (>= v 0)} */ = 0,
      node /*: Ref(~htmlElt) */ = null;
  if (isArray(value)) {
    value = assumePackedValues();
    /*: b htmlElts */ "#thaw";
    /*: value lvalue */ "#thaw";
    if (value.length !== b.length) {
      //PV: added calls to intToString
      error('ADsafe: Array length: ' + intToString(b.length) + '-' + intToString(value.length));
    }
    /*: ( htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro, 
          lvalue: {Arr(Top)|(packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      /*: node htmlElt */ "#thaw";
      if (node.tagname) {
        node.checked = !!value[i];
      }
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
    }
    /*: value (~lPackedValues, thwd lvalue) */ "#freeze";
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  else {
    /*: b htmlElts */ "#thaw";
    b.length;
    /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt )) | (packed v)} > lArrPro) -> sameType */
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
    (v :: (this: Ref(~lBunch!), value: Ref(~lNames!)) -> Ref(~lBunch) )
    (v :: (this: Ref(~lBunch!), value: Str) -> Ref(~lBunch) )
    )} */
{
  reject_global(this);
  /*: this lBunch */ "#thaw";
  var b  /*: Ref(~htmlElts) */ = this.___nodes___,
      i /*: {Int | (>= v 0)} */ = 0,
      node /*: Ref(~htmlElt) */ = null;

  var tmp1 /*: Int */ = 0;
  var tmp2 /*: Int */ = 0;
  var cond /*: Bool */ = true;

  if (isArray(value)) {
    value = assumeArray();
    
    ////PV: original code begin
    //if (value.length !== b.length) {
    //   error('ADsafe: Array length: ' + b.length + '-' +
    //      value.length);
    //        }
    ////PV: original code end

    /*: value lNames */ "#thaw";
    tmp1 = value.length;
    /*: value (~lNames, thwd lNames) */ "#freeze";
    
    /*: b htmlElts */ "#thaw";
    assume(b != null);
    tmp2 = b.length;
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

    ////XXX: SLOW DOWN !!!
    //if (tmp1 !== tmp2) {
    //  error('ADsafe: Array length: ' + int_to_string(tmp2) + '-' + int_to_string(tmp1));
    //}
    
    cond = i < tmp2; 
    
    assume(b != undefined);

    /*: (&value: Ref(~lNames)) -> sameType */ 
    for (i = 0; cond; i += 1) {
      ////TODO: RegEx support needed      
      //if (/url/i.test(string_check(value[i]))) {
      //  error('ADsafe error.');
      //}
      
      ////PV: original code begin 
      //node = b[i];
      //if (node.tagName) {
      //    node.className = value[i];
      //}
      ////PV: original code end
             
      /*: b htmlElts */ "#thaw";
      assume(b != null);
      assume(i < b.length);
      node = b[i];
      cond = i < b.length;
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

      /*: value lNames2 */ "#thaw";
      assume(value != null);
      assume(i < value.length);
      if (node.tagName) {
        node.className = value[i];
      }
      /*: value (~lNames, thwd lNames2) */ "#freeze";
    }
  }
  else {
    ////TODO: RegEx support needed      
    //if (/url/i.test(string_check(value))) {
    //  error('ADsafe error.');
    //}
    assume(typeof value === "string");

    /*: b htmlElts */ "#thaw";
    assume(b != null);
    /*: (htmlElts: {Arr(Ref(~htmlElt)) | (packed v)} > lArrPro) -> sameType */
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      if (node.tagName) {
        node.className = value;
      }
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  return this;
};
