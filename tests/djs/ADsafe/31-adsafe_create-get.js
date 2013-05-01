/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var error = /*: ()  -> { FLS } */ "#extern";

var reject_global = 
/*: {(and
(*      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)  
      (v::(that:Ref(~lO)) -> Top) *)
      (v::(that:Top) -> Top)
    )} */ "#extern";


/*: tyObject  
      { Dict | (and
              (not (has v "hasOwnProperty"))
              (implies (has v "create") ((sel v "create")::(Top) -> Top))
              (has v "prototype") (Dict (sel v "prototype"))
            )} > lObjPro */ "#define";

var banned = /*: lBanned */ {
      'arguments'     : true,
      callee          : true,
      caller          : true,
      constructor     : true,
      'eval'          : true,
      prototype       : true,
      stack           : true,
      unwatch         : true,
      valueOf         : true,
      watch           : true
    };

var reject_property = 
  /*: (object: Top, name_: Str) -> 
      { 
        (implies  
          (falsy v)
          (and 
            (= (tag object) "object")
            (not (= name_ "arguments"   ))
            (not (= name_ "callee"      ))
            (not (= name_ "caller"      ))
            (not (= name_ "constructor" ))
            (not (= name_ "prototype"   ))
            (not (= name_ "stack"       ))
            (not (= name_ "eval"        ))
            (not (= name_ "unwatch"     ))
            (not (= name_ "valueOf"     ))
            (not (= name_ "watch"       ))
          )
        )
      } */ "#extern";

//--------------------------------------------------------


var Object_ = {};
var hasOwnProperty_ = 
/*: {(and
      (v :: (this:Ref, kk:Str) / (this: dd:Dict > this.pro)
         -> {Bool|(iff (= v true) (has dd {kk}))} / same)
      (v :: [A] (this:Ref, kk:Str) / (this: Arr(A) > this.pro)
         -> {Bool|(iff (= v true) (= kk "length"))} / same)
      (v :: [A] (this:Ref, i:Int) / (this: aa:Arr(A) > this.pro)
         -> {Bool|(implies (and (packed aa) (>= i 0))
                    (iff (= v true) (< i (len aa))))} / same)
                    )} */ "#extern"; 


var getObjectPrototype = /*: [;L] () / () -> Ref(L) / (L: Top > lObjPro) */ "#extern";

Object_.hasOwnProperty = hasOwnProperty_;
Object_.prototype = /*: [;l] */ getObjectPrototype();

////XXX: This definition was originally here, but the type annotation for &F does
////not get added to the type signature of `create` correctly, so moving the
////definition within `create`
//function F() /*: new (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ {
//  return this;
//};


/*: (~lObjGeneral: Top > lObjPro) */ "#weak";


var create = function (o)  /*: [;L,Lp] (o: Ref) / (o: Top > lObjPro, l: Top > lObjPro) -> Top / () */
{
  reject_global(o);
  //PV: original code begin  
  //  if (Object.hasOwnProperty('create')) {
  //    return Object.create(o);                //PV: original
  //  }
  //PV: original code end

  if (Object_.hasOwnProperty('create')) {
    assert(false);
    return Object_.create(o);
  }

  function F() /*: new (this:Ref) / (this: Empty > this.pro) -> Ref(this) / same */ {
    return this;
  };

  //PV: original code begin  
  //F.prototype = (typeof o === 'object' && o) ? o : Object_.prototype;
  //PV: original code ends

  var tmp /*: Ref(~lObjGeneral) */ = null;

  if (typeof o === 'object') {
    /*: o (~lObjGeneral, frzn) */ "#freeze";
    tmp = o;
  }
  else {
    var op = Object_.prototype;
    /*: op (~lObjGeneral, frzn) */ "#freeze";
    tmp = op;
  }
//TODO
//  /*: tmp ltmp */ "#thaw";  
  
//  F.prototype = tmp;
//
//  var ret = new /*: L > ltmp */ F();
//  /*: tmp (~lObjGeneral, thwd ltmp) */ "#freeze";
//
  //return ret;
};

//  ADSAFE.get retrieves a value from an object.

var get = function (object, name) 
/*: (object: Ref, name: Str) / (object: Dict > object.pro) -> Top / sameExact */ 
{

  //PV: adding this:
  var arguments_ = /*: largs {Arr(Top)|(= (len v) 2)} */  [object,name];

  reject_global(object);
  if (arguments_.length === 2 && !reject_property(object, name)) {
    return object[name];
  }
  error();
};

var object = {};
object["callee"] = 1;
