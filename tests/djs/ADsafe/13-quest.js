/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star   /*: Bool */         = "#extern";
var name   /*: {(or (Str v) (= v null))} */ = "#extern";
var result /*: Ref(~lNodes) */ = "#extern";

//XXX: Not the exact inferred type for hunter
var hunter = {
               empty_  : function(n) /*: (Ref(~lNode)) -> Top */{ },
               plus    : function(n) /*: (Ref(~lNode)) -> Top */{ },
               greater : function(n) /*: (Ref(~lNode)) -> Top */{ },
               pound   : function(n) /*: (Ref(~lNode)) -> Top */{ },
               slash   : function(n) /*: (Ref(~lNode)) -> Top */{ },
               star    : function(n) /*: (Ref(~lNode)) -> Top */{ }
              };

var quest = function(query, nodes) 
  /*: (Ref(~lQuery), Ref(~lNodes)) -> Ref(~lNodes) */ 
{
  var selector /*: Ref(~lSelector) */ = null; 

//  var func /*: (Ref(~lNode)) -> Top */ = function(node) /*: (Ref(~lNode)) -> Top */ { };

  var i /*: { Int | (>= v 0) } */ = 0,
      j /*: { Int | (>= v 0) } */ = 0;

  // Step through each selector.

  /*: query lQuery */ "#thaw";
  query.length;

  /*: ( 
    &result: Ref(~lNodes), 
    &query: Ref(lQuery), lQuery: {Arr(Ref(~lSelector))|(packed v)} > lArrPro
    ) -> sameType  */
  for (i = 0; i < query.length; i += 1) {
    selector = query[0];

    /*: selector lSelector */ "#thaw";
    assert(/*: {(or (= v null) (Str v))} */ (selector.name));
    name = selector.name;
    
    assert(/*:  {(or (= v "empty_") 
                        (= v "plus") 
                        (= v "greater") 
                        (= v "pound") 
                        (= v "slash") 
                        (= v "star"))} */ (selector.op));
//TODO: arrow subtyping
    //func = hunter[selector.op];
    //assert(/*: (Ref(~lNode)) -> Top */ (hunter[selector.op]));
   
    /*: selector (~lSelector, thwd lSelector) */ "#freeze";   

    // There are two kinds of selectors: hunters and peckers. If this is a hunter,
    // loop through the the nodes, passing each node to the hunter function.
    // Accumulate all the nodes it finds.

//    if (typeof func === 'function') {
//      if (star) {
//        //TODO: expects query and nodes frozen
//        //error("ADsafe: Query violation: *" + selector.op +
//        //    (selector.name || ''));
//      }
//      result = [];
//
//      /*: (&nodes: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) |(packed v)} > lArrPro) 
//        -> sameType */
//      for (j = 0; j < nodes.length; j += 1) {
//        func(nodes[j]);
//      }
//    }
//    else {
//
//      // If this is a pecker, get its function. There is a special case for
//      // the :first and :rest selectors because they are so simple.
//
//      value = selector.value;
//      flipflop = false;
//      func = pecker[selector.op];
//      if (typeof func !== 'function') {
//        switch (selector.op) {
//          case ':first':
//              result = nodes.slice(0, 1);
//              break;
//          case ':rest':
//              result = nodes.slice(1, nodes.length);    //PV: added 2nd argument to slice
//              break;
//          default:
//              error('ADsafe: Query violation: :' + selector.op);
//        }
//      } 
//      else {
//
//        // For the other selectors, make an array of nodes that are filtered by
//        // the pecker function.
//
//        result = [];
//        /*: (&nodes: Ref(lNodes), lNodes: {Arr(Ref(~lNode)) |(packed v)} > lArrPro) 
//          -> sameType */
//        for (j = 0; j < nodes.length; j += 1) {
//          if (func(nodes[j])) {
//            result.push(nodes[j]);
//          }
//        }
//      }
//    }
//    nodes = result;

  }

  /*: query (~lQuery, thwd lQuery) */ "#freeze";

  return result;
};
