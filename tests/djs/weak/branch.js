/*: (~l |-> Top > lObjPro) */ "#weak";

var foo = function(x,b) /*: (x:Ref(~l), b:Bool) / (~l |-> frzn) -> Top / same */ {
  if (x == null) return;
  /*: x l */ "#thaw";
  if (b) { /*: x (~l, thwd l) */ "#freeze"; }
  else   { /*: x (~l, thwd l) */ "#freeze"; }
};
