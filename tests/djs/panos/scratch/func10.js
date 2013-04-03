//TODO: TC this

/*: (~lWindow: {
    setTimeout: (this:Ref(~lWindow), (this:Top)  -> Top , Num) -> Top,
    setInterval: (this: Top, (this: Top) / (~lWindow: frzn) -> Top / sameType, Num) -> Int,    
    clearInterval: (this:Top, Num) -> Top, 
    document: Ref(~lNode)
  } > lObjPro)
*/ "#weak";

var window = /*: Ref(~lWindow) */ "#extern";

var ina  = window.setInterval(
    function() /*: (this: Top) -> Top */ {
      window.clearInterval(ina);
    },
    1000);
