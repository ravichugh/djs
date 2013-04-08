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


///*: bar :: ({Str|(isPublic v)}, {Str|(isSecret v)}) -> Top */ "#type";
/*: bar :: (Str, {(= v "1")}) -> Top */ "#type";

var bar = function(pub, sec) {

  var obj = {};

  obj[sec] = sec;

  //assert(/*: {(isSecret v)} */ (obj[sec]));
  assert(obj[sec] == "1" );

  obj[pub] = pub;

  //TODO: this should fail!!!
  assert(obj[sec] == "1" );

  //This should fail !!!
//  assert(/*: {(isSecret v)} */ (obj[sec]));

};
