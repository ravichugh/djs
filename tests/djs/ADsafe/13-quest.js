var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: tySimpleHunter
    { Dict | (and
        (dom v {"empty_"}) ((sel v "empty_")::(Ref(~lNode)) -> Top)
    )} */ "#define";

var hunter /*: Ref tySimpleHunter */ = {}; //"#extern";
/*: tyPecker {
    dot        : (Ref(~lNode)) -> Bool ,
    amber      : (Ref(~lNode)) -> Bool ,
    underscore : (Ref(~lNode)) -> Bool ,
    lbrack     : (Ref(~lNode)) -> Bool ,
    lbrackeq   : (Ref(~lNode)) -> Bool ,
    s1         : (Ref(~lNode)) -> Bool ,
    s2         : (Ref(~lNode)) -> Bool ,
    s3         : (Ref(~lNode)) -> Bool ,
    s4         : (Ref(~lNode)) -> Bool ,
    s5         : (Ref(~lNode)) -> Bool ,
    s6         : (Ref(~lNode)) -> Bool ,
    blur       : (Ref(~lNode)) -> Bool ,
    checked    : (Ref(~lNode)) -> Bool ,
    disabled   : (Ref(~lNode)) -> Top  ,
    enabled    : (Ref(~lNode)) -> Top  ,
    even       : (Ref(~lNode)) -> Bool ,
    focus      : (Ref(~lNode)) -> Bool ,
    hidden     : (Ref(~lNode)) -> Top  ,
    odd        : (Ref(~lNode)) -> Bool ,
    tag_       : (Ref(~lNode)) -> Str  ,
    text       : (Ref(~lNode)) -> Bool ,
    trim       : (Ref(~lNode)) -> Bool ,
    unchecked  : (Ref(~lNode)) -> Top  ,
    visible    : (Ref(~lNode)) -> Top
  } */ "#define"; 

var pecker /*: Ref tyPecker */  = {}; //"#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star   /*: Bool */         = "#extern";
var name   /*: {(or (Str v) (= v undefined))} */ = "#extern";
var result /*: Ref(~lNodes) */ = "#extern";
var value  /*: {(or (Str v) (= v undefined))} */ = "#extern";
var flipflop /*: Bool */ = "#extern";

var quest = function(query, nodes) 
  /*: (Ref(~lQuery), Ref(~lNodes)) -> Ref(~lNodes) */
{
  var selector /*: Ref(~lSelector) */ = null;

  var cond /*: Bool */ = true;  //PV: adding this
  var elt  /*: Ref(~lNode) */ = null;

  var i /*: { Int | (>= v 0) } */ = 0,
      j /*: { Int | (>= v 0) } */ = 0;

  // Step through each selector.

  /*: query lQuery */ "#thaw";
  query.length;

  /*: ( &nodes: Ref(~lNodes),
        &query: Ref(lQuery), lQuery: {Arr(Ref(~lSelector))|(packed v)} > lArrPro
      )
      -> sameType  */
  for (i = 0; i < query.length; i += 1) {
    selector = query[0];
    /*: selector lSelector */ "#thaw";
    name = selector.name;
    var func = hunter[selector.op];
    
    /*: selector (~lSelector, thwd lSelector) */ "#freeze";   

    // There are two kinds of selectors: hunters and peckers. If this is a hunter,
    // loop through the the nodes, passing each node to the hunter function.
    // Accumulate all the nodes it finds.

    if (typeof func === 'function') {
//
//      if (star) {
//        error("ADsafe: Query violation: *" + selector.op +
//            (selector.name || ''));
//      }
//
//      /*: result lResult */ "#thaw";
//      result = /*: lResultEmpty {Arr(Ref(~lNode))|(packed v)} */ [];
//      /*: result (~lNodes, thwd lResult) */ "#freeze";
//      
//      /*:  nodes  lNodes */ "#thaw";
//      cond = i < nodes.length; 
//      /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
//
//      /*: ( &nodes: Ref(~lNodes)) -> sameType */
//      for (j = 0; cond; j += 1) {
//        /*: nodes lNodes */ "#thaw";
//        cond = j < nodes.length;
//        if (j < nodes.length) {
//          var nn = nodes[j];
//          /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
////TODO:           
////          func(nn);
//        }
//        else {
//          /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
//        }
//      }
    }
    else {

      // If this is a pecker, get its function. There is a special case for
      // the :first and :rest selectors because they are so simple.

      /*: selector lSelector */ "#thaw";
      assume(selector != null);
      value = selector.value;
      flipflop = false;
      assert(/*: Str */ (selector.op));
//TODO
//      func = pecker[selector.op];
      /*: selector (~lSelector, thwd lSelector) */ "#freeze"; 
      if (typeof func !== 'function') {
//TODO: switch
//        switch (selector.op) {
//          case ':first':
//              assume(nodes != null);
//              result = nodes.slice(0, 1);
//              break;
//          case ':rest':
//              /*: nodes lNodes */ "#thaw";
//              assume(nodes != null);
//              result = nodes.slice(1, nodes.length);    //PV: added 2nd argument to slice
//              /*: nodes (~lNodes, thwd lNodes) */ "#freeze"; 
//              break;
//          default:
//              error('ADsafe: Query violation: :' + selector.op);
//        }
      }
      else {

        // For the other selectors, make an array of nodes that are filtered by
        // the pecker function.

        /*: result lResult */ "#thaw";
        result = /*: lResultEmpty {Arr(Ref(~lNode))|(packed v)} */ [];
        /*: result (~lNodes, thwd lResult) */ "#freeze";

        /*:  nodes  lNodes */ "#thaw";
        cond = i < nodes.length; 
        /*: nodes (~lNodes, thwd lNodes) */ "#freeze";

        /*: (&nodes: Ref(~lNodes)) -> sameType */
        for (j = 0; cond; j += 1) {
          /*: nodes lNodes */ "#thaw";
          cond = j < nodes.length;
          if (j < nodes.length) {
            elt = nodes[j];
            /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
//TODO: func call
//            if (func(elt)) {
              /*: result lNodes */ "#thaw";
              result.push(elt);
              /*: result (~lNodes, thwd lNodes) */ "#freeze";
//            }
          }                 
          else {
            /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
          }
        }
      }
    }
    nodes = result;
  }
  /*: query (~lQuery, thwd lQuery) */ "#freeze";
  return result;
};
