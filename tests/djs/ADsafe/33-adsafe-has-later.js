/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var adsafe_id /*: Ref(~lId) */ = "#extern";
var adsafe_lib /*: Ref(~lLib) */ = "#extern";

var document  = /*: Ref(~lDocument) */ "#extern";

var error = /*: ()  -> { FLS } */ "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var owns = 
/*: (object: Ref, string: Str) / (object: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
    { (implies (= v true) (has d {string}))} / sameType */ "#extern";

var setTimeout = /*: (func: {(= (tag v) "function")}, timeout: Int) -> Top */ "#extern";

// --------------------------------------------------------------------------

var has = function (object, name) 
/*: (object: Ref, name: Str) / (object: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
    { (implies (= v true) (has d {name}))} / sameType */
{
  return owns(object, name);
};

  //  ADSAFE.id allows a guest widget to indicate that it wants to load
  //  ADsafe approved libraries.

var id = function (id) 
/*: (id: Ref(~lId)) -> Top */ 
{

  //  Calls to ADSAFE.id must be balanced with calls to ADSAFE.go.
  //  Only one id can be active at a time.

  if (adsafe_id) {
    error();
  }
  adsafe_id = id;
  
  var tmp = /*: ltmp {} */ {};
  /*: tmp (~lLib, frzn) */ "#freeze";
  adsafe_lib = tmp;
};


  //  ADSAFE.isArray returns true if the operand is an array.

var isArray_ =  isArray || function (value) /*: (Top) -> Bool */ {
//TODO
//  return Object.prototype.toString.apply(value) === '[object Array]';
  return false;
};


  //  ADSAFE.keys returns an array of keys.

var keys = 
//TODO
//  Object.keys || 
  function (object) 
/*: (object:Ref) / (object: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> Ref(~lKeys) / sameType */
  {
    var key /*: Str */ = "", result = /*: lRes {Arr(Str)|(packed v)} */ [];
    /*: ( &object: Ref(Lobject), Lobject: {Dict|(not (has v "hasOwnProperty"))} > lObjPro, 
          lRes:{Arr(Str)|(and (packed v))} > lArrPro)
          -> sameType */
    for (key in object) {
      if (owns(object, key)) {
        result.push(key);
      }
    }
    /*: result (~lKeys, frzn) */ "#freeze";
    return result;
  };


  //  ADSAFE.later calls a function at a later time.

var later = function (func, timeout) 
/*: (func: Top, timeout: Int) -> Top */
{
  if (typeof func === 'function') {
    setTimeout(func, timeout || 0);
  } else {
    error();
  }
};


