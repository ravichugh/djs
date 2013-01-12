var foo = function () 
  /*: () -> Top */
{
  var i /*: {Int | (>= v 0)} */ = 0;
  var v = 5;
  // This is how you define an abstract array location (see langParser.mly:
  // jsArrLit)

  var mat = /*: lMat Arr(Int) */ [];
  var arr = /*: lArr Arr(Int) */ [];
  mat[0] = 0; mat[1] = 1; mat[2] = 2; mat[3] = 3; mat[4] = 4;



  
  /*: (lArr : Arr(Int) > lArrPro) -> sameType */
    //This works cause the it does not require to preserve the same exact value in
    //pointed by lArr, just the type.
    // This is wrong:  /*: (lArr : Arr(Int) > lArrPro) -> sameExact */
    // This means that the value stored in lArr shall remain unmodified
  for (i = 0; i < v; i++) {
    var j = mat[i];
    arr[0] = 1;
  };
  return v;

};

