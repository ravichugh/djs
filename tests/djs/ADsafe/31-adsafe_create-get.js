/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: ()  -> { FLS } */ "#extern";

var reject_global = 
/*: {(and
(*      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)  *)
      (v::(that:Ref(~lO)) -> Top)
    )} */ "#extern";

function F() /*: (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ {
//  var self = this;
//  /*: self (~lF,frzn) */ "#freeze";
//  return self; 
//  //PV: added body
  return this;
};


/*: tyObject  
      { Dict | (and
              (not (has v "hasOwnProperty"))
              (implies (has v "create") ((sel v "create")::(Top) -> Top))
              (has v "prototype") (Dict (sel v "prototype"))
            )} > lObjPro */ "#define";

//--------------------------------------------------------


var create = function (o, object)   //PV: adding 2nd argument
/*: (o:Ref(~lO), object: Ref) / (object: tyObject) -> Top / () */
{
  reject_global(o);
//  if (Object.hasOwnProperty('create')) {    //PV: original
  if (object.hasOwnProperty('create')) {
//    return Object.create(o);                //PV: original
    return object.create(o);
  }
//  F.prototype = typeof o === 'object' && o ? o : Object.prototype;    //PV: original
//  return new F();
};

//  ADSAFE.get retrieves a value from an object.

var get = function (object, name) 
/*: (object: Ref(~lO), name: Str) -> Top / sameType */ 
{
  reject_global(object);
//  if (arguments.length === 2 && !reject_property(object, name)) {
//    return object[name];
//  }
  error();
};

