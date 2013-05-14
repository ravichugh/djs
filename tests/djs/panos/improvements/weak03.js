
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";


var foo = function(a,b) /*: (a: Ref(~htmlElts!), b: Ref(~htmlElts!)) -> Top */ {
  
  var i /*: {Int|(>= v 0)} */ = 0;
  var j /*: {Int|(>= v 0)} */ = 0;

  var l;
  
  /*: b htmlElts */ "#thaw";
  l = b.length;
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";

  for (i = 0; i <= 10; i++) {
  
    
  
  
  }


};
