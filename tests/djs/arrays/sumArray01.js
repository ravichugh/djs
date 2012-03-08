var sumPackedArray = function(ns) /*:
  [;L] [[ns:Ref(L)]]
     / [L |-> (_:{(and (v::Arr(Int)) (packed v))}, lArrayProto)]
    -> Int / same */
{
    var sum = 0;
    var i = 0;
    var n = ns.length;
    /*: [&i |-> _:{Int|(>= v 0)}, &sum |-> _:Int, &ns |-> _:Ref(L),
         &n |-> _:{Int|(= v (len a))},
         L |-> (a:{(and (v::Arr(Int)) (packed v))}, lArrayProto)]
     -> [&i |-> _:{Int|(>= v 0)}, &sum |-> _:Int, &ns |-> _:Ref(L),
         &n |-> _:{Int|(= v (len ns))},
         L |-> (a':{(= v a)}, lArrayProto)] */
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
