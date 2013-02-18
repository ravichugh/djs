/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var adsafe_id /*: Ref(~lId) */ = "#extern";
var adsafe_lib /*: Ref(~lLib) */ = "#extern";

var document  = /*: Ref(~lDocument) */ "#extern";

var error = /*: {(and (v::() -> { FLS }) (v::(Str)-> {FLS}))} */ "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var reject_name = /*: (name1: Str) -> { (implies  (falsy v)
      (and (not (= name1 "arguments"))(not (= name1 "callee"))(not (= name1 "caller"))
      (not (= name1 "constructor")) (not (= name1 "prototype"))(not (= name1 "stack"))
      (not (= name1 "eval"))(not (= name1 "unwatch")) (not (= name1 "valueOf"))
      (not (= name1 "watch")) )) }  */ "#extern";

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

var reject_property = /*: (object: Top, name: Str) -> Top */ "#extern";

var owns = 
/*: (object: Ref, string: Str) / (object: d: {Dict|(not (has v "hasOwnProperty"))} > lObjPro) -> 
    { (implies (= v true) (has d {string}))} / sameType */ "#extern";

var setTimeout = /*: (func: {(= (tag v) "function")}, timeout: Int) -> Top */ "#extern";

var arguments /*: Ref(lArr) */ = "#extern";


//PV: using a more imprecise type here, to TC _intercept
/*: tyInterceptor {Arr({(= (tag v) "function")})|(and (packed v))} */ "#define";

var interceptors = /*: lIC tyInterceptor */ [];

// --------------------------------------------------------------------------
  //  ADSAFE.lib allows an approved ADsafe library to make itself available
  //  to a widget. The library provides a name and a function. The result of
  //  calling that function will be made available to the widget via the name.
  
var lib = function (name, f) 
/*: (Str, (Ref(~lLib)) -> Top) -> Top */
{
  if (!adsafe_id || reject_name(name)) {
    error("ADsafe lib violation.");
  }
  adsafe_lib[name] = f(adsafe_lib);
};


  //  ADSAFE.log is a debugging aid that spams text to the browser's log.
  //  Overwrite this function to send log matter somewhere else.
    
var log = function log(s)
/*: (Str) -> Top */ 
{
//TODO: stupid function
//  if (window.console) {
//    console.log(s);        /* Firebug */
//  } else if (typeof Debug === 'object') {
//    Debug.writeln(s);      /* IE */
//  } else if (typeof opera === 'opera') {
//    opera.postError(s);    /* Opera */
//  }
};


  //  ADSAFE.remove deletes a value from an object.

var remove = function (object, name)
/*: (object: Ref, name: Str) / (object: d: Dict > lObjPro) -> Top / sameType */
{
  //TODO: arguments
//  if (arguments.length === 2 && !reject_property(object, name)) {
//    delete object[name];
//    return;
//  }
  error();
};


  //  ADSAFE.set stores a value in an object.
    
var set = function (object, name, value) 
/*: (object: Ref, name: Str, value: Str) 
    / (object: d: Dict > lObjPro, lArr: {Arr(Str)|(packed v)} > lArrPro) 
    -> Top / sameType */
{
  ( /*: [;Lobject,lObjPro;] */ reject_global)(object);
  if (arguments.length === 3 && !reject_property(object, name)) {
    object[name] = value;
    return;
  }
  error();
};

  //  ADSAFE._intercept allows the page to register a function that will
  //  see the widget's capabilities.

var _intercept = function (f) 
/*: (f: {(= (tag v) "function")}) -> Top */
{
  interceptors.push(f);
};


