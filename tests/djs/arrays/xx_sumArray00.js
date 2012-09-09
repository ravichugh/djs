var sumPackedArray = function(ns) /*:
  [;L] (ns:Ref(L)) / (L |-> _:{(and (v::Arr(Int)) (packed v))} > lArrPro)
    -> Int / same */
{
    var sum = 0;
    var i;

    /*: (&i |-> _:{Int|(>= v 0)}, &sum |-> _:Int, &ns |-> _:Ref(L),
         L |-> a:{(and (v::Arr(Int)) (packed v))} > lArrPro)
     -> (&i |-> _:{Int|(>= v 0)}, &sum |-> _:Int, &ns |-> _:Ref(L),
         L |-> a':{(= v a)} > lArrPro) */
    for (i=0; i < ns.length; i++)
        sum += ns[i+1];   // NOTE: bad index

    return sum;
};
