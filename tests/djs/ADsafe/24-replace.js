/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyBunchObj { "___nodes___": Ref(~htmlElts), "___star___": Bool} > lObjPro */ "#define";
/*: tyBunchArr { Arr(Ref(~lBunch))|(packed v)} > lArrPro */ "#define";


var error = /*: (message: Str)  -> { FLS } */ "#extern";

var star /*: Bool */ = "#extern";
var value /*: Str */ = "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var purge_event_handlers = /*: (node: Ref(~htmlElt)) -> Top */ "#extern";


var array_check  = function(a) /*: [;L;] (a: Ref(L)) / (L: tyBunchArr) -> Top / sameExact */ {};

var object_check = function(a) /*: [;L;] (a: Ref(L)) / (L: tyBunchObj) -> Top / sameExact */ {};

var int_to_string = /*: (Int) -> Str */ "#extern";



//--------------------------------------------------------------

var replace = function (replacement)
/* {(and
        (v:: (this: Ref(~lBunch), replacement: Ref(lA)) / (lA: tyBunchArr) -> Top / sameExact )
        (v:: (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact )
    )} */

//PV: both work if you disable the right part that should be dead code in each
//case. 
/*:  (this: Ref(~lBunch), replacement: Ref(lA)) / (lA: tyBunchArr) -> Top / sameExact */
/* (this: Ref(~lBunch), replacement: Ref(lO)) / (lO: tyBunchObj) -> Top / sameExact */
{
  reject_global(this);
  var b = this.___nodes___,
      flag /*: Bool */ = false,
      i /*: { Int | (>= v 0)} */ = 0,
      j /*: { Int | (>= v 0)} */ = 0,
      newnode /*: Ref(~htmlElt) */ = null,
      node /*: Ref(~htmlElt) */ = null,
      parent /*: Ref(~htmlElt) */ = null,
      rep /*: Ref(~htmlElts) */ = null;
  
  var cond /*: Bool */ = true;   //PV: added this
  
  /*: b htmlElts */ "#thaw";
  if (b.length === 0) {
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    return;
  }
  else {
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }

  /*: b htmlElts */ "#thaw";
  /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
      -> sameType */ 
  for (i = 0; i < b.length; i += 1) {
    purge_event_handlers(b[i]);
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";


  if (    !replacement 
      ||  replacement.length === 0 
//PV: original code had the following - moved it in an else-if branch
/*    ||  (replacement.___nodes___ && replacement.___nodes___.length === 0) */
    )
  {
    /*: b htmlElts */ "#thaw";
    /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
      -> sameType */ 
    for (i = 0; i < b.length; i += 1) {
      node = b[i];
      purge_event_handlers(node);
      if (node.parentNode) {
        node.parentNode.removeChild(node);
      }
    }
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  }
  else if (replacement.___nodes___) {

    var rn /*: Ref(~htmlElts) */ = replacement.___nodes___;
    /*: rn lRepNodes */ "#thaw";  
    if (rn.length === 0) {
      /*: rn (~htmlElts, thwd lRepNodes) */ "#freeze";

      /*: b htmlElts */ "#thaw";
      /*: ( &i:i0:{Int|(>= v 0)}, &b: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro)
        -> sameType */ 
      for (i = 0; i < b.length; i += 1) {
        node = b[i];
        purge_event_handlers(node);
        if (node.parentNode) {
          node.parentNode.removeChild(node);
        }
      }
      /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    }
    else {
      /*: rn (~htmlElts, thwd lRepNodes) */ "#freeze";
    }

  }
  else if (isArray(replacement)) {

    /*: b htmlElts */ "#thaw";
    if (replacement.length !== b.length) {
      //TODO: these are supposed to be arguments in error(...) 
      int_to_string(b.length);
      int_to_string(value.length);
      error('ADsafe: Array length: ');
    }
    else {
    }

    //PV: added extra condition - might be able to infer this
    cond = i < b.length && i < replacement.length;
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

    /*: (&b: Ref(~htmlElts)) -> sameType */ 
    for (i = 0; cond; i += 1) {
      /*: b htmlElts */ "#thaw";
      cond = i < b.length && i < replacement.length;
      if (i < b.length) {
        node = b[i];
        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
      //  /*: node htmlElt */ "#thaw";
        parent = node.parentNode;
      //  /*: node (~htmlElt, thwd htmlElt) */ "#freeze";

        purge_event_handlers(node);

        if (parent) {
          if (i < replacement.length) {
            rep = replacement[i].___nodes___;
            
            /*: rep htmlElts */ "#thaw";
            if (rep.length > 0) {
              newnode = rep[0];
              parent.replaceChild(newnode, node);
              /*: (&rep: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) -> sameExact */ 
              for (j = 1; j < rep.length; j += 1) {
                node = newnode;
                newnode = rep[j];
                parent.insertBefore(newnode, node.nextSibling);
              }
            }
            /*: rep (~htmlElts, thwd htmlElts) */ "#freeze";
          } else {
            parent.removeChild(node);
          }
        }

      }
      else {
        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
      }

    }
  } 
//  else {
//    rep = replacement.___nodes___;
//    /*: b htmlElts */ "#thaw";
//    cond = i < b.length;
//    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//
//    /*: (&b: Ref(~htmlElts)) -> sameType */
//    for (i = 0; cond; i += 1) {
//
//      /*: b htmlElts */ "#thaw";
//      cond = i < b.length;
//      if (i < b.length) {
//        node = b[i];
//        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//        purge_event_handlers(node);
//        parent = node.parentNode;
//
//        if (parent) {
//          /*: rep htmlElts */ "#thaw";
//          assume(rep != null);
//          //PV: To ensure that rep[0] is not undefined 
//          assume(rep[0] != undefined);
//          newnode = flag ? rep[0].cloneNode(true) : rep[0];
//          parent.replaceChild(newnode, node);
//          
//          /*: (&rep: Ref(htmlElts), htmlElts: {Arr(Ref(~htmlElt))|(packed v)} > lArrPro) -> sameExact */ 
//          for (j = 1; j < rep.length; j += 1) {
//            node = newnode;
//            newnode = flag ? rep[j].clone(true) : rep[j];
//            parent.insertBefore(newnode, node.nextSibling);
//          }
//          flag = true;
//          /*: rep (~htmlElts, thwd htmlElts) */ "#freeze";
//        }
//
//      }
//      else {
//        /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
//      }
//    }
//  }
//
  return this;
};

