/*: "tests/djs/sif/__mozilla.dref" */ "#use";


// DJS DEFINITIONS BEGIN
var require = 
  /*: [;L;] ({Str|(= v "chrome")}) / () -> Ref(L) / 
  (L: { Cc: Ref(~lComponents_classes), 
        Ci: Ref(~lComponents_interfaces)} > lObjPro) */ "#extern";


var exports = /*: Ref(~extern) */ "#extern";


// DJS DEFINITIONS END


// SECURITY PROPERTIES BEGIN

/*: (implies (isPrivileged v) (isTainted v)) */ "#assume";

/*: (forall (d f) 
      (implies 
        (and (has v f) (isPrivileged (sel v f))) 
        (isPrivileged d)
      )
    ) */ "#assume";

//NOT WORKING:
// /*: (implies (v :: Ref(~nsIPrefBranch)) ({Ref(~nsIPrefBranch)|(isPrivileged v)} v)) */ "#assume";
//
// /*: (implies (v :: (Top) -> {(isPrivileged v)}) (isPrivileged v)) */ "#assume";



// SECURITY PROPERTIES END



  
///PV: Desuraging destructuring assignment:
///var {Cc, Ci} = require("chrome");
var a = (/*: [;l;] */ require)("chrome");

assert(/*: Ref(~lComponents_classes) */ (a.Cc));
assert(/*: Ref(~lComponents_interfaces) */ (a.Ci));

var Cc = a.Cc;
var Ci = a.Ci;




//Ugly hack to get this type to work ... 
var tmp =  /*: {Ref(~nsIPrefBranch)|(isPrivileged v)} */ "#extern";


var Preferences = /*: lP */ { };
Preferences._branches = 
/*  lB { Dict | (forall (s) (implies (has v s) ((sel v s) :: Ref(~nsIPrefBranch))))} */
/*: lB { s: {Ref(~nsIPrefBranch)|(isPrivileged v)}, _: Bot} */ { s: tmp }; 

Preferences._caches = { };


Preferences.getBranch = function (name) 
/*: (Str) / ( &Preferences: Ref(lP), 
              lP: {_branches: Ref(lB)} > lObjPro, 
              (*lB: { Dict | (forall (s) (implies (has v s) ({Ref(~nsIPrefBranch)|(isPrivileged v)} (sel v s))))} > lObjPro)*)
              lB: { s: {Ref(~nsIPrefBranch)|(isPrivileged v)}, _: Bot} > lObjPro)
    -> { Ref(~nsIPrefBranch) | (isPrivileged v) } / 
      (&Preferences: Ref(lP), lP: Dict > lObjPro, lB: Dict > lObjPro) */  

{
  if (name in Preferences._branches && name != "hasOwnProperty") {
  /*
   *
   * Original code was the following commented line. 
   *
   *  if (name in this._branches)
   *
   * "hasOwnProperty" is hard-coded in every prototype object so the "in" check
   * will always succeed for this field. If you want to impose a type for all
   * fields present in the object you need to check that the field is not
   * "hasOwnProperty".
   *
   * Could have gotten the same guarantee just by adding an assume statement. 
   *
   */

    assert(/*: {Ref(~nsIPrefBranch)|(isPrivileged v)} */ (Preferences._branches[name]));
    return Preferences._branches[name]; 
  }; 
  
  var branch =
      Cc["mozilla_org__preferences_service_1"]
      .getService(Ci.nsIPrefService).getBranch(name);
//  assert(/*: {Ref(~nsIPrefBranch)|TRU} */ (branch));
//  assert(/*: {Ref(~nsIPrefBranch)|(isPrivileged v)} */ (branch));
  Preferences._branches[name] = branch;
  return Preferences._branches[name];
  
};

/* other properties */


assert(/*: {(isPrivileged v)} */  (Preferences.getBranch("aa")));
//assert(/*: {(v :: (Top) -> Top)} */  (Preferences.getBranch));



//exports.Preferences = Preferences;
