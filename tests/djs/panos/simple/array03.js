
//To assert that an arary is packed, just pass it to this function as parameter.
var dummy = function(a) 
/*:[;Le;] (a: Ref(Le)) / (Le : {(and (v::Arr(NotUndef)) (packed v))} > lArrPro ) -> Top / same */
{ };

var makePacked = function(n) 
/*: [;L;] (n: {Int | (>= n 0)}) / ()  -> 
    Ref(L) / (L: {(and (v::Arr(NotUndef)) (packed v) (= (len v) n))} > lArrPro ) */ 
{
  var i = 0;
  var a  = /*: L */ [];
  //a[0] = 0; a[1] = 0; a[2] = 0; a[3] = 0; //these preserve packedness
  /*: ( &i : i0: {Int | (and (>= v 0) (<= v n))},
        L : {(and (v::Arr(NotUndef)) (packed v) (= (len v) i0))} > lArrPro)
      ->
      ( &i: {Int | (= v n)},
        L : {(and (v::Arr(NotUndef)) (packed v) (= (len v) n))} > lArrPro))   
  */ 
  for ( ; i < n; i++) {
    a[i] = i;  
  }  
  return a;
};
//print(makePacked(5));

var a = (/*: [;l;] */ makePacked)(5);
