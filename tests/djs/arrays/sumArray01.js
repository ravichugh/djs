var sumPackedArray = function(ns) /*:
  [;L] (ns:Ref(L)) / (L |-> _:{(and (v::Arr(Int)) (packed v))} > lArrPro)
    -> Int / sameType */
{
    var sum = 0;
    var i;

    /*: (&i |-> _:{Int|(>= v 0)}, &sum |-> _:Int, &ns |-> _:Ref(L),
         L |-> _:{(and (v::Arr(Int)) (packed v))} > lArrPro)
     -> sameType */
    for (i=0; i < ns.length; i++)
        sum += ns[i];

    return sum;
};

var arr = (/*: Arr(Int) */ []);

sumPackedArray(arr);

arr.push(1);
arr.push(2);
arr.push(3);

sumPackedArray(arr);
