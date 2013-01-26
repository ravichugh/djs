/*: (~lA : Dict > lObjPro) */ "#weak";
/*: (~lMatch    : { Arr(Str) | (and (packed v) (>= (len v) 0)) }  > lArrPro) */ "#weak"; 

var t = "aa";
var a /*: Ref(~lA) */ = null; 
var match /*: Ref(~lMatch) */ = null;

/*: (&t: t0: Str) -> 
    (&t: t1: Str) */ 
while(t) {

  /*: match lMatch */ "#thaw";
  match = /*: Arr(Str)*/ ["a", "b", "c"];    //Without the annotation: Arr(NotUndef) is assumed which is not a supertype of Arr(Str)

  var b = match[1];
  
  if (b) {
    /*: a lA */ "#thaw";
    a = { op: "sss" }; 
    /*: a (~lA, thwd lA) */ "#freeze";
  }
  /*: match (~lMatch, thwd lMatch) */ "#freeze";
  
  t = t.slice(1,2);

} ;
