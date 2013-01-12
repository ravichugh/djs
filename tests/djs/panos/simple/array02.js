/*: helper :: (x: Int, acc: Int) -> Int */ "#type";
var helper = function(x, acc) {
  return x + acc;
};

/*: fold :: [A,B;L;] (mat: Ref(L), x0: B, f: (B, A) -> B)
        / (L: {(and (v::Arr(A)) (packed v) (> (len v) 0) )} > lArrPro) 
        -> B / same */ "#type";
var fold = function (mat, x0, f)
{
  var i;
  var acc = x0;
  var v = mat.length;

  assert( /*: B */  (acc));

  /*: (
      &i   |-> { Int | (and (>= v 0) )},
      &mat |-> Ref(L),
      &acc |-> _:B
      )
        ->
      (
      &i   |-> { Int | (and (>= v 0) )},
      &mat |-> _:Ref(L),
      &acc |-> _:B 
      )
      */
  for (i = 0; i < v; i++) {
    acc = f(acc, mat[i]);
  };

  return acc;

};

var dummy = function(a) /*: [A] (a:Ref) / (a: {Arr(A) | (packed v)}  > lArrPro) -> Top / same */  {


};

var a = /*: lA */ [0,1];
dummy(a);

// (/*: [Int, Int; lA ]  */ fold) (a, 0, helper);

