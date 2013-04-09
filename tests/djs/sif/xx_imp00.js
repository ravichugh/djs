/**************************************************
 *                                                *
 *      Implicit leak via dynamic fields          *          
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

  obj[pub] = 1;     //The object has at least one public key

  obj[sec] = 1;     //And at least one secret key

  //So the WHOLE object is considered secret:
  //The following call should succeed
  testSec(obj);

                  
  if ("1" in obj) {
    assert(/*: {(isSecret v)} */ (obj["1"]));
    window.public = obj["1"];
  }


};
