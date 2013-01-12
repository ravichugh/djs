var foo = function () /*: () -> Top */
{
  var i ;
  var v = 5;
  var mat = /*: lMat Arr(Int) */ [];
  var arr = /*: lArr Arr(Int) */ [];
  mat[0] = 0; mat[1] = 1; mat[2] = 2; mat[3] = 3; mat[4] = 4;

  /*: ( lArr : Arr(Int) > lArrPro, 
        &i:  i0: Int ) 
      -> 
      ( lArr : Arr(Int) > lArrPro, 
        &i : {Int | (ite (>= i0 0) (= v (- 0 1)) (= v i0))} )
  */
  for (i = v-1; i >= 0; i = i -1) {
    var j = mat[i];
  };
  return v;
};

