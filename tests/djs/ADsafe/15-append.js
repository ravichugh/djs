/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";
var star  /*: Bool */               = "#extern";
var value /*: Str */              = "#extern";

var int_to_string /*: (Int) -> Str */ = "#extern";


var foo = function(a)
/*: [;L;] (a: Ref(L)) / (L: {Arr(Ref(~lBunch)) | (packed v)} > lArrPro) -> Top / sameType */ { };


var append = function (appendage) 
/*: {(and
    (v :: (this: Ref(~lBunch), appendage: Ref(lArr)) / (lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), appendage: Ref(lBunchObj)) / (lBunchObj: {"___nodes___": Ref(~lNodes) } > lObjPro ) -> Ref(~lBunch) /sameType)
    )} */
{
  //TODO: TC reject_global
  //reject_global(this);
  var b = this.___nodes___,
      flag /*: Bool */ = false,
      i /*: {Int | (>= v 0)}*/ = 0 ,
      j /*: {Int | (>= v 0)}*/ = 0 ,
      node /*: Ref(~lNode) */ = null,
      rep /*: Ref(~lNodes) */ = null;

  /*: b lNodes */ "#thaw";
  var b_len = b.length;
  //PV: replacing b.length with b_len
  var cond = b_len === 0;
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  if (cond || !appendage) {
    return this;
  }

  /*: b lNodes */ "#thaw";

  //if (appendage instanceof Array) {   //XXX: original code
  if (isArray(appendage)) {
    if (appendage.length !== b.length) {
      //XXX: expects ~lNodes to be frozen
      //error('ADsafe: Array length: '+ int_to_string(b_len) + '-' +
      //    int_to_string(value.length) );
    }

    assert( /*: Ref(lArr)*/ (appendage));

    //for (i = 0; i < b.length; i += 1) {           //XXX: original code
    for (i = 0; i < appendage.length; i += 1) {     //changed to this to ensure bound check!!!
      var bch = appendage[i];
      assert(/*: Ref(~lBunch) */ (bch));
      ///*: bch lBunch */ "#thaw";
      //rep = bch.___nodes___;

      //TODO: Will have to have rep and b thawed to make the assignment
      //for (j = 0; j < rep.length; j += 1) {
      //  b[i].appendChild(rep[j]);
      //}
      ///*: bch (~lBunch, thwd lBunch) */ "#freeze";
    }
  } 
  else {
    rep = appendage.___nodes___;
    assert(/*: Ref(lNodes) */ (b));
    assert(/*: Ref(~lNodes) */ (rep));
    /*: (lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      //TODO: Will have to have rep and b thawed to make the assignment
      //for (j = 0; j < rep.length; j += 1) {
      //  node.appendChild(flag
      //      ? rep[j].cloneNode(true)
      //      : rep[j]);
      //}
      flag = true;
    }
  }
        
 /*: b (~lNodes, thwd lNodes) */ "#freeze";

  return this;
};

