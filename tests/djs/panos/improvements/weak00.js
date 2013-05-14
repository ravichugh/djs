/*: (~w: Dict > lObjPro) */ "#weak";
/*: (~ar: {Arr(Int)|(packed v)} > lArrPro) */ "#weak";


var bar = function(a,b) /*: (a:Ref(~w), b: Ref(~w)) -> Ref(~w) */ {
 

  var f = /*: lArr {Arr(Int)|(packed v)} */ [1];

  /*: f (~ar, frzn) */ "#freeze";

  //assume(f != null);


  /*: f lArr */ "#thaw";
  
  /*: f (~ar, thwd lArr) */ "#freeze";

  return a;
};
