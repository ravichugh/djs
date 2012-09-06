var sumTriple = function(x) /*:
  [;Lx;] (x:Ref(Lx))
       / (Lx |-> a:{(and (v::Arr(Int)) (packed v) (= (len v) 3))} > lArrPro)
      -> Int / same */ {
  return x[0] + x[1] + x[2];
};

var a = /*: lA Arr(Int) */ [10,20,30];
var b = /*: lB Arr(Int) */ [10,20,30,40];

/*: [;lA;] */ sumTriple(a);

/// this version allows x to have _more_ than 3 elements
var sumThree = function(x) /*:
  [;Lx;] (x:Ref(Lx))
       / (Lx |-> a:{(and (v::Arr(Int)) (packed v) (>= (len v) 3))} > lArrPro)
      -> Int / same */ {
  return x[0] + x[1] + x[2];
};

/*: [;lA;] */ sumThree(a);
/*: [;lB;] */ sumThree(b);
