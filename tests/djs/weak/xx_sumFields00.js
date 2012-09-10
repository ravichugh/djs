/*: (~lObj |-> {Dict|(Int (sel v "n"))} > lObjPro) */ "#weak";

var sumFields = function(objs) /*:
  [;Larr] (objs:Ref(Larr))
        / (~lObj |-> frzn,
           Larr |-> array:{(and (v::Arr(Ref(~lObj))) (packed v))} > lArrPro)
       -> Int / same */
{
  var i = 0, n = 0;
  /*: loopAnn -> sameType */
  for (i=-1; i < objs.length; i++) { // BAD: i isn't >= 0
    var obj = objs[i];
    /*: obj lThaw */ "#thaw";
    n += obj.n;
    /*: obj (~lObj, thwd lThaw) */ "#freeze";
  }
  return n;
};

/*: #define loopAnn (
      &i    |-> _:{Int|(>= v 0)},
      &n    |-> _:Int,
      &objs |-> _:Ref(Larr),
      Larr  |-> _:{(= v array)} > lArrPro,
      ~lObj |-> frzn
) */ "#define";
