/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var reject_global = function(that) 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */
{
  if (that.window) {
    return error("default");   //PV: Adding "default" message
  }
};
