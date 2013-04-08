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


/*: bar :: [;L;] (Ref(L) , {Str|(isSecret v)})
    / (L: {Dict|(isPublic v)} > lObjPro) -> Top / sameType */ "#type";

var bar = function(obj, secret) {

  /* The following should not be allowed: a public object cannot be 
   * accessed through a secret field value. */
  obj[secret] = 1;

//  public = obj["1"];

};
