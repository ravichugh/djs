var row1 = /*: lRow */ ["0","1"];
var mat = /*: lMat */ [row1, row1];
var i = 0;
var j = 0;

/*: outerLoop -> sameType */
for (; i < mat.length; i++) {
  /*: innerLoop -> sameType */
  for (; j < 3; j++) { // BAD: guard should be j < 2
    assert (/*: Str */ (mat[i][j]));
  }
}

/*: #define outerLoop (
       &mat  |-> _:Ref(lMat),
       lMat  |-> _:<Ref(lRow),Ref(lRow)> > lArrPro,
       lRow  |-> _:<Str,Str> > lArrPro,
       &i    |-> _:{Int|(>= v 0)},
       &j    |-> _:{Int|(>= v 0)}
) */ "#define";

/*: #define innerLoop (
       &mat  |-> _:Ref(lMat),
       lMat  |-> innerMat:<Ref(lRow),Ref(lRow)> > lArrPro,
       lRow  |-> _:<Str,Str> > lArrPro,
       &i    |-> _:{Int|(and (>= v 0) (< v (len innerMat)))},
       &j    |-> _:{Int|(and (>= v 0))}
) */ "#define";
