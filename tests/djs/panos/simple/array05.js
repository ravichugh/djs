/*: tyArr {Arr(Int)|(packed v)} > lArrPro */ "#define";
/*: (~lArr : tyArr) */ "#weak";



var c /*: Ref(~lArr) */  = null;

var i /*: { Int | (>= v 0) } */ = 0;

/* ( &c: {(or (v:: Ref(lArr0)) (v:: Ref(lArr1)) ) }, lArr0: tyArr, lArr1: tyArr) -> 
    ( &c: {(v:: Ref(lArr1)) }, lArr1: tyArr)   
 */
for(i = 0; i <= 10; i++)  {
  /*: c lArr */ "#thaw";
  c = /*: lArr1 Arr(Int) */  [];
  /*: c (~lArr, thwd lArr) */ "#freeze";


  c.push(1);

};
