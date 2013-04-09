/**************************************************
 *                                                *
 *  Explicit leak via prototype-based inheritance *          
 *                                                *
 * ***********************************************/

/*: "tests/djs/sif/__sif.dref" */ "#use";

/*: (forall (s) (implies (isPublic s) (isSecret s))) */ "#assume";

var bar = function(window, x, sec, pub) 
/*: [;L;] (Ref(~window), Ref(L), {(isSecret v)}, {(isPublic v)})
    / (L: Dict > lObjPro) 
    -> Top / sameType */ 
{
  
  var obj = {};

  assert(!("foo" in obj));

  //XXX: This won't work like it's suppose to in JS -- need to use beget. 
  obj.__proto__ = x; 

  x.foo = pub;

  assert(/*: {(isSecret v)} */ (x.foo));
  
//  assert(/*: {(isSecret v)} */ (obj.foo));
  
  window.public = obj.foo;
};


