var row1 = /*: lRow */ ["0","1"];

// putting the same strong reference in the array, to test out looping
var mat = /*: lMat */ [row1, row1];
var i;

/*: heapAnn -> heapAnn */
for (i=0; i < mat.length; i++) {
  assert (/*: Str */ (mat[i][0]));
}

/*: #define heapAnn
    (&i    |-> _:{Int|(>= v 0)},
     &mat  |-> _:Ref(lMat),
     &row1 |-> _:Ref(lRow),
     lRow  |-> _:<Str,Str> > lArrPro,
     lMat  |-> _:<Ref(lRow), Ref(lRow)> > lArrPro) */ '#define';
