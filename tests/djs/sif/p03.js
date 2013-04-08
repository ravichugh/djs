/**************************************************
 *                                                *
 *      Implicit leak via dynamic fields          *          
 *                                                *
 * ***********************************************/


/* In a public object, disallow the assignment of secret fields */
/*: (forall (d f) 
      (implies 
        (and (isPublic d) (has d f))
        (isPublic (sel d f))
      )
    )*/ "#assume";


/*: bar :: [;L;] (Ref(L) , {Str|(isPublic v)})
    / (L:d:{ Dict | (isPublic d) } > lObjPro) -> Top / sameType */ "#type";

var bar = function(obj, pub) {

  assert(/*: {(isPublic v)} */ (pub));

  obj[pub] = 1;


};
