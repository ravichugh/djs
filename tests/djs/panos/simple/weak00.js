/*: (~lA : Dict > lObjPro) */ "#weak";
/*: (~lMatch    : Arr(Str) > lArrPro) */ "#weak"; 

var t = "aa";
var a /*: Ref(~lA) */ = null; 
var match /*: Ref(~lMatch) */ = null;

/*: (&t: t0: Str) -> 
    (&t: t1: Str) */ 
while(t) {

  /*: a lA */ "#thaw";
  a = { op: "sss" }; 
  /*: a (~lA, thwd lA) */ "#freeze";

  /*: match lMatch */ "#thaw";
  match = /*: Arr(Str)*/ ["a", "b", "c"];    //PV: temporarily using this 
  /*: match (~lMatch, thwd lMatch) */ "#freeze";
  
  t = t.slice(1);

} ;
