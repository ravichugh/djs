var sumTriple = function(x) /*:
  [;Lx;] (x:Ref(Lx)) / (Lx |-> a:<Int,Int,Int> > lArrPro)
      -> Int / same */ {
  return x[0] + x[1] + x[2];
};

var a = [10,20,30];
var b = [10,20,30,40];

sumTriple(a);

/// this version allows x to have _more_ than 3 elements
var sumThree = function(x) /*:
  [;Lx;] (x:Ref(Lx)) / (Lx |-> a:<Int,Int,Int,...> > lArrPro)
      -> Int / same */ {
  return x[0] + x[1] + x[2];
};

sumThree(a);
sumThree(b);
