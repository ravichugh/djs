var foo = function(a) 
/*: (a:Ref) / (a: Top > a.pro) -> Top / sameType */
/* (Ref(~arr)) -> Top */ { };

/*: (~arr: Arr(Int) > lArrPro) */ "#weak";

var baz = function() /*: () -> Top  */ { };

var bar = function(a,b)
/* [;L] (Ref(L), Bool) / (L: Arr(Int) > lArrPro) -> Top / (L: frzn) */ 
/*: (Ref(~arr), Bool) -> Top */ 
{

  var vv =  a;

  if (b) {
    var tmp = /*: l1 Arr(Int) */ [];
    /*: tmp (~arr, frzn) */ "#freeze";
    vv = tmp;
  };

//
//  //baz();
//  
  /*: vv ltotal */ "#thaw";
  assume(vv != null);

  vv.length;


//  /*: [;ltotal,lArrPro] */  foo(vv);
  /*: vv (~arr, thwd ltotal) */ "#freeze";


};

