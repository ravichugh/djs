var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";
var int_to_string /*: (Int) -> Str */ = "#extern";

var assumeArray   = /*: ()-> Ref(~lBunches) */ "#extern";
var assumeObject  = /*: ()-> Ref(~lBunch) */ "#extern";


/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star  /*: Bool */ = "#extern";
var value /*: Str */ = "#extern";

var reject_global = 
/*: [;L1,L2;] (that: Ref(L1)) / (L1:d:Dict > L2, ~lBunch: thwd lBunch) 
    -> {(implies (truthy (objsel d "window" cur L2)) FLS)} / sameExact */ "#extern";


var append = function (appendage) 
/*: {(and 
          (v:: (this: Ref(~lBunch), appendage: Ref(~lBunches)) -> Ref(~lBunch)) 
          (v:: (this: Ref(~lBunch), appendage: Ref(~lBunch)) -> Ref(~lBunch))
    )} */

{
  /*: this lBunch */ "#thaw";
  assume(this != null);
  reject_global(this);
  /*: this (~lBunch, thwd lBunch) */ "#freeze";

  var b /*: Ref(~htmlElts) */ = this.___nodes___,
      flag /*: Bool */ = false,
      i /*: {Int | (>= v 0)}*/ = 0 ,
      j /*: {Int | (>= v 0)}*/ = 0 ,
      node /*: Ref(~htmlElt) */ = null,
      rep /*: Ref(~htmlElts) */ = null;

  var tmp0 /*: Int */ = 0;
  var tmp1 /*: Int */ = 0;
  var tmp2 /*: Int */ = 0;

  var cond /*: Bool */ = true;

  /*: b htmlElts */ "#thaw";
  cond = b.length === 0;
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

  if (cond || !appendage) {
    return this;
  }



  if (isArray(appendage)) {

    appendage = assumeArray();
    
    /*: appendage lBunches */ "#thaw";
    assume(appendage != null);
    tmp1 = appendage.length;
    /*: appendage (~lBunches, thwd lBunches) */ "#freeze";
    
    /*: b htmlElts */ "#thaw";
    assume(b != null);
    tmp2 = b.lenght;
    tmp2 = 0;
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

    if (tmp1 !== tmp2) {
      error('ADsafe: Array length: ' + int_to_string(tmp2) + '-' + int_to_string(value.length));
    }
    cond = i < tmp2 && i < tmp1; 
    
    //PV: Original code begin
    //for (i = 0; i < b.length; i += 1) {
    //  rep = appendage[i].___nodes___;
    //  for (j = 0; j < rep.length; j += 1) {
    //    b[i].appendChild(rep[j]);
    //  }
    //}
    //PV: Original code end
            
    /*: appendage lBunches */ "#thaw";
    assume(appendage != null);

    /*: (&appendage: Ref(lBunches), lBunches: {Arr(Ref(~lBunch))|(packed v)} > lArrPro)
          -> sameType */ 
    for (i = 0; i < appendage.length && cond ; i += 1) {
      
      /*: b htmlElts */ "#thaw";
      assume(i < b.length);
      var bi = b[i];
      cond = i < b.length;
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
        
      assume(i < appendage.length);
      rep = appendage[i].___nodes___;
      assert(/*: Ref(~htmlElts) */ (rep));
      
      /*: rep lRep */ "#thaw";
      assume(rep != null);
      /*: ( &rep: Ref(lRep), lRep: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
          -> sameType */
      for (j = 0; j < rep.length; j += 1) {
        bi.appendChild(rep[j]);
      }
      /*: rep (~htmlElts, thwd lRep) */ "#freeze";
    }
    /*: appendage (~lBunches, thwd lBunches) */ "#freeze";

  }
  else {
    appendage = assumeObject();
    assert(/*: Ref(~lBunch) */ (appendage));
    
    /*: appendage lB */ "#thaw";
    assume(appendage != null);
    rep = appendage.___nodes___;
    /*: appendage (~lBunch, thwd lB) */ "#freeze";

    /*: b bElts */ "#thaw";
    assume(b != null);
    tmp2 = b.length; 
    /*: b (~htmlElts, thwd bElts) */ "#freeze";

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

