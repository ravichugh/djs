var sumPackedArray = function(ns) /*:
  [;L] (ns:Ref(L)) / (L |-> array:{(and (v::Arr(Int)) (packed v))} > lArrPro)
    -> Int / sameExact */
{
    var sum = 0;
    var i = 0;
    var n = ns.length;
    /*: (&i |-> _:{Int|(>= v 0)}, &sum |-> _:Int, &ns |-> _:Ref(L),
         &n |-> _:{Int|(= v (len array))}, L |-> _:{(= v array)} > lArrPro)
     ->  sameType */
    for (; i < n; i++)
        sum += ns[i];

    return sum;
};

var arr = (/*: Arr(Int) */ []);

sumPackedArray(arr);

arr.push(1);
arr.push(2);
arr.push(3);

sumPackedArray(arr);
