var foo = function(a) 
/*: (a:Ref) / (a: Top > a.pro) -> Top / sameExact */
{

};

/*: (~arr: Arr(Int) > lArrPro) */ "#weak";

var baz = function() /*: () -> Top  */ { };

var bar = function(b,a)
/*: [;L] (Bool, Ref(L)) / (L: Arr(Int) > lArrPro) -> Top / sameType */ {

  var vv =  a;
  /*: vv (~arr, frzn) */ "#freeze";

  if (b) {
    vv = /*: l1 Arr(Int) */ [];
    /*: vv (~arr, frzn) */ "#freeze";
  };

  

//  assume(vv != null);

  //baz();
  
  /*: vv ltotal */ "#thaw";
  assume(vv != null);
  /*: [;ltotal,lArrPro] */ foo(vv);
  /*: vv (~arr, thwd ltotal) */ "#freeze";


};

