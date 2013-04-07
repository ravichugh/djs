/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var hunter = {
  '': function () /*: () -> Top */ { }
};


var quest = function(query) /*: (Ref(~lQuery)) -> Top */ 
{

  var i /*: { Int | (>= v 0) } */ = 0,
      selector /*: Ref(~lSelector) */ = null,
      func /*: () -> Top */ = function() /*: () -> Top */  { } ;

  /*: query lQuery */ "#thaw";
  var len = query.length;
  /*: query (~lQuery, thwd lQuery) */ "#freeze";

  /*: (&query: Ref(~lQuery)) -> sameType  */
  for (i = 0; i < len; i += 1) {

    func = function() /*: () -> Top */ {};
//    
//    /*: query lQuery */ "#thaw";
//    if (i < query.length)   //PV: added this check
//      selector = query[i];
//    /*: query (~lQuery, thwd lQuery) */ "#freeze";
//
//    if (selector.op == '') 
//      func = hunter[selector.op];
  }
};
