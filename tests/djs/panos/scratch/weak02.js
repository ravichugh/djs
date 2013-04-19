var foo = function(a) 
/*: (a:Ref) / (a: Top > a.pro) -> Top / sameExact */
{

};

/*: (~arr: Arr(Int) > lArrPro) */ "#weak";

var baz = function() /*: () / (~arr: thwd ltotal) -> Top / sameExact */ { };

var bar = function(b) /*: (Bool) -> Top */ {

  var vv;

  if (b) {
    vv = /*: l2 Arr(Int) */ [1];
    /*: vv (~arr, frzn) */ "#freeze";
  }
  else {
    vv = /*: l1 Arr(Int) */ [];
    /*: vv (~arr, frzn) */ "#freeze";
  };

  
  /*: vv ltotal */ "#thaw";


  assume(vv != null);



  baz();

  /*: [;ltotal,lArrPro] */ foo(vv);

  /*: vv (~arr, thwd ltotal) */ "#freeze";


};

