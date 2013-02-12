/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star   /*: Bool */         = "#extern";
var name   /*: Str */          = "#extern";
var result /*: Ref(~lNodes) */ = "#extern";
var hunter = "#extern";

var quest = function(query, nodes) 
  //XXX: Not the exact inferred type for hunter
  /*: [;L;] (Ref(~lQuery), Ref(~lNodes)) /
    ( &hunter: Ref(L), L: {
        empty_  : (Ref(~lNode)) -> Top ,
        plus    : (Ref(~lNode)) -> Top ,
        greater : (Ref(~lNode)) -> Top ,
        pound   : (Ref(~lNode)) -> Top ,
        slash   : (Ref(~lNode)) -> Top ,
        star    : (Ref(~lNode)) -> Top ,
        _       : Bot
      } > lObjPro)  
    -> Ref(~lNodes) / sameType */ 
{
  var selector /*: Ref(~lSelector) */ = null; 

//  var func /*: (Ref(~lNode)) -> Top */ = 
//    function(node) /*: (Ref(~lNode)) -> Top */ { };

//  var func;

  var i /*: { Int | (>= v 0) } */ = 0,
      j /*: { Int | (>= v 0) } */ = 0;

  // Step through each selector.

  //TRICK: does not TC without query.length and nodes.length
  /*: query lQuery */ "#thaw";
  query.length;

  /*: ( 
    &result: Ref(~lNodes), 
    &query: Ref(lQuery), lQuery: {Arr(Ref(~lSelector))|(packed v)} > lArrPro, 
    &name: Str
    ) -> sameType  */
  for (i = 0; i < query.length; i += 1) {
    selector = query[0];
    var s = query[0];
//    name = selector.name;
    
    assert(/*:  {(or (= v "empty_") 
                        (= v "plus") 
                        (= v "greater") 
                        (= v "pound") 
                        (= v "slash") 
                        (= v "star"))} */ (selector.op));
    //func = hunter[selector.op];
    //assert(/*: (Ref(~lNode)) -> Top */ (hunter[selector.op]));
    hunter[selector.op];
    
    
    

//    // There are two kinds of selectors: hunters and peckers. If this is a hunter,
//    // loop through the the nodes, passing each node to the hunter function.
//    // Accumulate all the nodes it finds.
//
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
//      //                    value = selector.value;
//      //                    flipflop = false;
//      //                    func = pecker[selector.op];
//      if (typeof func !== 'function') {
//        //                        switch (selector.op) {
//        //                        case ':first':
//        //                            result = nodes.slice(0, 1);
//        //                            break;
//        //                        case ':rest':
//        //                            result = nodes.slice(1, nodes.length);    //PV: added 2nd argument to slice
//        //                            break;
//        //                        default:
//        //                            error('ADsafe: Query violation: :' + selector.op);
//        //                        }
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
