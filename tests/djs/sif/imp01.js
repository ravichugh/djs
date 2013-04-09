/*************************************************
 *                                                *
 *        Implicit leak via conditional           *
 *                                                *
 * ***********************************************/

/*: "tests/djs/sif/__sif.dref" */ "#use";

/*: (forall (s) (implies (isPublic s) (isSecret s))) */ "#assume";

/* In a public object, disallow the assignment of secret fields */

/*: (forall (d f)
      (implies 
        (isSecret f)
        (implies (has d f) (isSecret d))
      )
    )*/ "#assume";

/*: (forall (d f)
      (implies 
        (isSecret d)
        (implies (has d f) (isSecret (sel d f)))
      )
    ) */ "#assume";


/*: PStr {Str | (isPublic v)} */ "#define";
/*: SStr {Str | (isSecret v)} */ "#define";



var testSec = function(o) /*: [;L;] (Ref(L)) / (L: {Dict|(isSecret v)} > lObjPro) -> Top / sameType */ {};


/*: bar :: (Ref(~window), SStr, PStr) -> Top */ "#type";
var bar = function(window, sec, pub) {

  var obj = {};


  if (sec == "1") {
    window.public = 1;  
  }


};


