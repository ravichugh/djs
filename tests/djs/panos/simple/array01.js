// Force the loop to be executed at least once.

//We need to give the type for the loop such a form so that if the value 
//for i is such that the loop is not taken, we force j to get the type that we
//want it to have. This way it's like faking that it's going to be executed.
//E.g. while (i < 1) {j = 17; i +=;} :: 
///*: (&i |-> i0:Int, &j: {i0 >=1 => v = 17})-> (&i |-> Int, &j : {v = 17})

var foo = function (mat) 
/*: [A;L, Ly;] (mat: Ref(L)) / 
      (L: {(and (v::Arr(A)) (packed v) (> (len v) 0))} > lArrPro) -> 
      A / same */
{
  var i = 0;
  var v = mat.length;
  assert(/*: {(> v 0)} */ (v));
  
  var j;
  /*: ( &i : i0 : Int,
        &j : j0:{(implies (> i0 0) (v::A))} )
        ->
      ( &i : sameType,
        &j : A )
  */
  while (i < mat.length) {
    j = mat[i];
    i = i + 1;
  };
  return j;
};
//print(foo(["aa"]));
