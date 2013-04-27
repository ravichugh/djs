 
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";


var foo = function(a)
/*:[;L;] (a: Ref(L)) / (L: Arr(Ref(~lNode)) > lArrPro ) -> Top /
sameType */ {};

var fun = function(b, n) 
/*: (b: Ref(htmlElts), n: Ref(~lNode)) / (htmlElts: {Arr(Ref(~lNode))|(packed v)} > lArrPro) -> Top / sameType*/ 
{
  var i /*: { Int | (>= v 0)} */ = 0;
  /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~lNode)) | (packed v)} > lArrPro) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    var bArr = /*: lBArr Arr(Ref(~lNode)) */  [n];
    /*: [;lBArr;] */ foo(bArr);
  }
};

var explode = function () 
/*: (this: Ref(~lBunch)) -> Ref(lA) */
{
  var a = /*: lA {Arr(Ref(~lBunch))|(packed v)} */ [];
  /*: this lBunch */ "#thaw";
  var b = this.___nodes___;
  /*: this (~lBunch, thwd lBunch) */ "#freeze";
  var i /*: { Int | (>= v 0)} */ = 0;

  /*: b htmlElts */ "#thaw";
  b.length;
  /*: (&b: Ref(htmlElts), htmlElts: {Arr(Ref(~lNode)) | (packed v)} > lArrPro,
       &a: Ref(lA), lA: Arr(Ref(~lBunch)) > lArrPro
      ) -> sameType */
  for (i = 0; i < b.length; i += 1) {
    var bArr = /*: lBArr Arr(Ref(~lNode)) */  [b[i]];
    /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
    /*: [;lBArr;] */ foo(bArr);

//    a[i] =  (new /*: lBch [;lBArr] */ Bunch)(bArr);
    /*: b htmlElts */ "#thaw";
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return a;
};

