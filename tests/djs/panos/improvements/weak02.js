/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var append = function (appendage) 
/*: (this: Ref(~lBunch!), appendage: Ref(~lBunch!)) -> Top */ 
{

  var rep;
    
  /*: appendage lB */ "#thaw";
  rep = appendage.___nodes___;
  /*: appendage (~lBunch, thwd lB) */ "#freeze";
};

