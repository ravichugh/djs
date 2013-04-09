/**************************************************
 *                                                *
 *      Explicit flow through prototype link      *
 *          Assigning a public variable 
 *              to a "secret" field*
 *                                                *
 * ***********************************************/

/*: "tests/djs/sif/__sif.dref" */ "#use";

/*: (forall (s) (implies (isPublic s) (isSecret s))) */ "#assume";

/*: beget :: [;LL1,LL2,LL3;]
    (Ref(LL2)) / (LL2: Top > LL3) -> Ref(LL1) / (LL1: Empty > LL2, LL2: same) */ '#type';
/*: ctor :: (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ '#type';
var beget = function (o) {
  function ctor() { return this; };
  ctor.prototype = o;
  return new /*: LL1 > LL2 */ ctor();
};


/*: bar :: [;L;] (Ref(~window), Ref(L), {(isSecret v)})
    / (L: { } > lObjPro) -> Top / sameType */ "#type";

var bar = function(window, x, sec) {
  var obj = /*: [;lObj, L, lObjPro;] */ beget(x);
  x.foo = sec;
  assert(/*: {(isSecret v)} */ (obj.foo));
  window.public = obj.foo;
};


