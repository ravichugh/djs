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
//TODO: this should work with an intersection type
/* (this: Ref(~lBunch), appendage: Ref(lArr)) 
    / (lArr: { Arr(Ref(~lBunch)) | (packed v) }  > lArrPro) 
    -> Ref(~lBunch) / sameType */ 

/*: (this: Ref(~lBunch), appendage: Ref(lBunchObj)) 
    / ( lBunchObj: {"___nodes___": Ref(~htmlElts) } > lObjPro) 
    -> Ref(~lBunch) /sameType */
{
  /*: this lBunch */ "#thaw";
  assume(this != null);
  reject_global(this);
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var b /* Ref(~htmlElts) */ = this.___nodes___,
      flag /*: Bool */ = false,
      i /*: {Int | (>= v 0)}*/ = 0 ,
      j /*: {Int | (>= v 0)}*/ = 0 ,
      node /*: Ref(~htmlElt) */ = null,
      rep /*: Ref(~htmlElts) */ = null;

  var cond /*: Bool */ = true;

  /*: b htmlElts */ "#thaw";
  cond = b.length === 0;
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  if (cond || !appendage) {
    return this;
  }


  if (isArray(appendage)) {
//    /*: b htmlElts */ "#thaw";
//    if (appendage.length !== b.length) {
//      error('ADsafe: Array length: ' + int_to_string(b.length) + '-' + int_to_string(value.length));
//    }
//    cond = i < b.length && i < appendage.length; 
//    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//
//    /*: (&b: Ref(~htmlElts), lArr: {Arr(Ref(~lBunch))|(packed v)} > lArrPro) -> sameType */
//    for (i = 0; cond ; i += 1) {
//      
//      /*: b htmlElts */ "#thaw";
//      if (i < b.length && i < appendage.length) {
//        cond = i < b.length && i < appendage.length;
//        var bi = b[i];
//        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//        
//        var bch = appendage[i];
//        rep = bch.___nodes___;
//        
//        /*: rep htmlElts */ "#thaw";
//        assume(rep != null);
//        /*: ( &rep: Ref(htmlElts), 
//              htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) 
//            -> sameType */
//        for (j = 0; j < rep.length; j += 1) {
//          bi.appendChild(rep[j]);
//        }
//        /*: rep (~htmlElts, thwd htmlElts) */ "#freeze";
//      }
//      else {
//        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//      }
//    }
  }
  else {

    /*: b htmlElts */ "#thaw";
    cond = i < b.length; 
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

    rep = appendage.___nodes___;
    /*: (&b: Ref(~htmlElts)) -> sameType */
    for (i = 0; cond; i += 1) {
      /*: b htmlElts */ "#thaw";
      if (i < b.length) {
        cond = i < b.length;
        node = b[i];
        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

        /*: rep htmlElts */ "#thaw";
        assume(rep != null);
        /*: ( &rep: Ref(htmlElts), 
              htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) 
            -> sameType */
        for (j = 0; j < rep.length; j += 1) {
          node.appendChild(flag
              ? rep[j].cloneNode(true)
              : rep[j]);
        }
        /*: rep (~htmlElts, thwd htmlElts) */ "#freeze";
        flag = true;
      }
      else {
        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
      }
    }
  }
        

  return this;
};

