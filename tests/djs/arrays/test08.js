var foo = function(x) /*:
  [;Lx;] (x:Ref(Lx)) / (Lx |-> a:<Bool,Int,Int> > lArrPro)
      -> Int / same */ {
  if (x[0]) return 1 + x[1];
  return 2 + x[2];
};
