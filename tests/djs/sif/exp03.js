/**************************************************
 *                                                *
 *      Explicit flow through array access        *
 *      Assigning and retrieving public data      *
 *                                                *
 * ***********************************************/

/*: "tests/djs/sif/__sif.dref" */ "#use";

/*: (forall (s) (implies (isPublic s) (isSecret s))) */ "#assume";

/*: NonNeg {Int | (>= v 0)} */ "#define";
/*: PStr {Str | (isPublic v)} */ "#define";
/*: SStr {Str | (isSecret v)} */ "#define";


/*: bar :: (Ref(~window), n: NonNeg, m: NonNeg, SStr, PStr) / () -> Top / (l: Top > lArrPro)  */ "#type";

var bar = function(window, n, m, sec, pub) {
  
  var a  = /*: l {Arr(Str)|(packed v)} */ [];

  var i = 0;

  /*: ( &i : i0: {Int | (and (>= v 0) (<= v n))},
        l : {(and (v::Arr(Str)) (packed v) (= (len v) i0))} > lArrPro)
      ->
      ( &i: {Int | (= v n)},
        l : {Arr(Str)|(and (packed v) (= (len v) n))} > lArrPro))   
  */ 
  for (; i < n; i++) {
    a[i] = pub;
  };


  if (n < a.length) {
    assert(/*: PStr */ (a[n])); //this also fails
    window.public = a[m];
  };

};


