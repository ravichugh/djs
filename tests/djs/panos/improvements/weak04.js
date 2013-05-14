
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";


var foo = function(a,b) /*: (a: Ref(~htmlElt!), b: Ref(~htmlElt!)) -> Top */ {
  
  var i /*: {Int|(>= v 0)} */ = 0;
  var j /*: {Int|(>= v 0)} */ = 0;

  var l;
  
  l = a.___nodes___; 
  
  /*: a htmlElt */ "#thaw";
  l = a.aaa;
  /*: a (~htmlElt, thwd htmlElt) */ "#freeze";



};
