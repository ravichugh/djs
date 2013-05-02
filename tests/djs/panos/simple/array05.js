/*: tyArr {Arr(Int)|(packed v)} > lArrPro */ "#define";


var c = /*: l0 {Arr(Int)|(packed v)} */ []; // /*: Ref(~lArr) */  = null;

var i /*: { Int | (>= v 0) } */ = 0;

/*: ( &c: {(or (v:: Ref(l0)) (v:: Ref(l1)) ) }) -> 
    ( &c: sameType ) */
for(i = 0; i <= 10; i++)  {
  c = /*: l1 {Arr(Int)|(packed v)} */  [];
};
