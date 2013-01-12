
/**
 *  The location variables declared at the definition of the type for beget
 *  correspond the exact number and order of actual location parameters that
 *  need to be provided at every call to beget. 
 *  - LL1: the returned location
 *  - LL2: the prototype used for LL1
 *  - LL3: the prototype used for Ll2
 *
 *  TODO Beget needs to know that LL2 is not null ??? Where do we get this from?
 *
 *  TODO Why do we need to specify LL3 - shouldn't it be able to infer it?
 *
 *
 */ 


/*: beget :: [;LL1,LL2,LL3;]
    (Ref(LL2)) / (LL2: Top > LL3) -> Ref(LL1) / (LL1: Empty > LL2, LL2: same) */ '#type';

/*: ctor :: (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ '#type';

var beget = function (o) {
  function ctor() { return this; };
  ctor.prototype = o;
  return new /*: LL1 > LL2 */ ctor();
};



//Need to specify which is location lX1 !!!
var x1 = /*: lX1 */ {a:1};


//Beget needs to know that x1 is not null
var x3 = /*: [ ;lX3, lX1, lObjPro ; ] */ beget(x1);

assert(x3 !== null);

/*
 * If we try to give the following statement,
 *
 * //  var x4 = />: [ ;lX4, lX3, lObjPro ; ] </ beget(x3);
 * 
 * then we get the error:
 *   proto links differ lX3 
 *
 * This means that we are trying to use the same protype fpr lX3 that has been
 * used before and therefore this is an error. 
 *
 * If we were to accept this statement this would imply that lX3 would have
 * lObjPro as its prototype which is not valid, because lX3 has lX1 as a
 * prototpe, and lobjPro is lX1's prototype. 
 *
 */


var dummy = /*: lDummy */ {};

var x4 = /*: [ ;lX4, lX3, lX1 ; ] */ beget(x3);
var x5 = /*: [ ;lX5, lX4, lX3 ; ] */ beget(x4);

var x6 = /*: [ ;lX6, lX1, lObjPro ; ] */ beget(x1);
x6.a = true;



/**
 * Joining environments with many possible prototype links is not allowed! 
 * So the code segment below would fail.
    //if (x1.a > 0) {
    //  x7 = [<: [ ;lX7, lX6, lX1 ; ] >] beget(x6);
    //  assert (typeof x7.a === "boolean");
    //}
    //else {
    //  x7 = [<: [ ;lX7, lX4, lX3 ; ] >] beget(x4);
    //  assert (typeof x7.a === "number");  
    //}
*
 * Determining the graph of prototype linking really is a pointer analysis
 * problem with the following properties:
 * - Every object has exactly one prototype. 
 * - Root of all prototypes is the location: lObjPro
 * - The graph is kept a tree by the constraint of having to specify the three
 *   locations [ ; LL1, LL2, LL3; ] where LL1 --> LL2 --> LL3 is a chain of
 *   prototypes. 
 * - For locations [ ; LL1, LL2, LL3; ] and [ ; LL1', LL2', LL3'; ] if is
 *   checked that: 
 *   LL1 == LL1' => (and (LL2 == LL2') (LL3 == LL3'))
 *    
 */

var x7 = /*: [ ;lX7, lX4, lX3 ; ] */ beget(x4);

var x8 = /*: [ ;lX8, lX7, lX4 ; ] */ beget(x7);



