/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

/*: tyArr {Arr(Int)|(packed v)} > lArrPro */ "#define";
/*: tyObj { nodes: {Arr(Int)|(packed v)}  }  > lObjPro */ "#define";

var foo = function(a)
/*: (a: {(and (v:: Ref(lA)) (v:: Ref(lO)))}) 
  / (lA: tyArr, lO: {nodes: Ref(lNodes)} > lObjPro, lNodes: Arr(Int) > lArrPro) -> Top / sameExact */
{
  
  a.length;

  if (isArray(a)) {
    assert(/*: Ref(lA) */ (a));
  }
  else {
    assert(/*: Ref(lO) */ (a));
    a.nodes.length;
  }


};

var bar = function(a)
/*: (a:Ref(lA)) / (lA: tyArr) -> Top / sameExact */
{
    assert(/*: Ref(lA) */ (a));
    a.nodes;
};

var baz = function(a)
/*: (a:Ref(lA)) / (lA: {Arr(Int)|(packed v)} > lArrPro) -> Top / sameExact */
{
  if (a.b && a.b.length === 0) {
  
  }
};

