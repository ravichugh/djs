var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
var int_to_string /*: (Int) -> Str */ = "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star  /*: Bool */ = "#extern";
var value /*: Str */ = "#extern";


var reject_global = 
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */ "#extern";

var foo = function(a)
/*: [;L;] (a: Ref(L)) / (L: {Arr(Ref(~lBunch)) | (packed v)} > lArrPro) -> Top / sameType */ { };


var append = function (appendage) 
/*: {(and
    (v :: (this: Ref(~lBunch), appendage: Ref(lArr)) / (lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro) -> Ref(~lBunch) / sameType)
    (v :: (this: Ref(~lBunch), appendage: Ref(lBunchObj)) / (lBunchObj: {"___nodes___": Ref(~lNodes) } > lObjPro, lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro ) -> Ref(~lBunch) /sameType) 
    )} */
{
  /*: this lBunch */ "#thaw";
  assume(this != null);
  reject_global(this);
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var b /* Ref(~lNodes) */ = this.___nodes___,
      flag /*: Bool */ = false,
      i /*: {Int | (>= v 0)}*/ = 0 ,
      j /*: {Int | (>= v 0)}*/ = 0 ,
      node /*: Ref(~lNode) */ = null,
      rep /*: Ref(~lNodes) */ = null;

  var cond_0 /*: Bool */ = true;
  var cond_1 /*: Bool */ = true;
  var cond_2 /*: Bool */ = true;

  /*: b lNodes */ "#thaw";
  cond_0 = b.length === 0;
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  if (cond_0 || !appendage) {
    return this;
  }


  if (isArray(appendage)) {
    assert(isArray(appendage));
    /*: b lNodes */ "#thaw";
//    if (appendage.length !== b.length) {
//      error('ADsafe: Array length: ... ');
////TODO      
////      error('ADsafe: Array length: ' + int_to_string(b.length) + '-' + int_to_string(value.length));
//    }
    cond_1 = i < b.length && i < appendage.length; 
    /*: b (~lNodes, thwd lNodes) */ "#freeze";
    

//TODO: if-false
//    /*: ( (*&b: Ref(lNodes), lNodes: {Arr(Ref(~lNode))|(and (packed v) )} > lArrPro,*)
//          &appendage: Ref(lArr), lArr: {Arr(Ref(~lBunch))|(packed v)} > lArrPro
//        ) -> sameExact */
//    for (i = 0; cond_1 ; i += 1) {
//      
//      /*: b lNodes */ "#thaw";
//      if (i < b.length && i < appendage.length) {
//        cond_1 = i < b.length && i < appendage.length;
//        /*: b (~lNodes, thwd lNodes) */ "#freeze";
//        
////        var bch = appendage[i];
////        rep = bch.___nodes___;
////        
////        /*: rep lNodes */ "#thaw";
////        cond_1 = j < rep.length;
////        /*: rep (~lNodes, thwd lNodes) */ "#freeze";
////
////        for (j = 0; cond_1; j += 1) {
////          b[i].appendChild(rep[j]);
////        }
//      }
//    }
  }
//  else {
//    rep = appendage.___nodes___;
//    assert(/*: Ref(lNodes) */ (b));
//    assert(/*: Ref(~lNodes) */ (rep));
//    /*: (lNodes: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */ 
//    for (i = 0; i < b.length; i += 1) {
//      node = b[i];
//      //TODO: Will have to have rep and b thawed to make the assignment
//      //for (j = 0; j < rep.length; j += 1) {
//      //  node.appendChild(flag
//      //      ? rep[j].cloneNode(true)
//      //      : rep[j]);
//      //}
//      flag = true;
//    }
//  }
        

  return this;
};

