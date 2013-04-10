/*: "tests/djs/sif/__mozilla.dref" */ "#use";

// DJS DEFINITIONS BEGIN
var require = 
  /*: [;L;] ({Str|(= v "chrome")}) / () -> Ref(L) / 
  (L: { Cc: Ref(~lComponents_classes), 
        Ci: Ref(~lComponents_interfaces)} > lObjPro) */ "#extern";

// DJS DEFINITIONS END


// SECURITY PROPERTIES BEGIN





// SECURITY PROPERTIES END


  
///PV: Desuraging destructuring assignment:
///var {Cc, Ci} = require("chrome");
var a = (/*: [;l;] */ require)("chrome");

assert(/*: Ref(~lComponents_classes) */ (a.Cc));
assert(/*: Ref(~lComponents_interfaces) */ (a.Ci));

var Cc = a.Cc;
var Ci = a.Ci;

var Preferences = /*: lP */ { };
Preferences._branches = 
/*: lB { s: Ref(~nsIPrefBranch), _:Bot } */ { };
Preferences._caches = { };

Preferences.getBranch = function (name) 
/*: (Str) / ( &Preferences: Ref(lP), 
              lP: {_branches: Ref(lB)} > lObjPro, 
              lB: {s: Ref(~nsIPrefBranch), _: Bot} > lObjPro) 
    -> Ref(~nsIPrefBranch) / 
      (&Preferences: Ref(lP), lP: Dict > lObjPro, lB: Dict > lObjPro) */  {

///  if (name in this.branches) return this._branches[name];

  if (name in Preferences._branches) { 
    assert(name in Preferences._branches);
    assert(/*: Ref(~nsIPrefBranch) */ (Preferences._branches[name]));
    //return Preferences._branches[name];
  };
  var branch = Cc["mozilla_org__preferences_service_1"]
    .getService(Ci.nsIPrefService).getBranch(name);

  assert(/*: Ref(~nsIPrefBranch) */ (branch));

  Preferences._branches[name] = branch;
  
  return Preferences._branches[name];
  
};

//  /* other properties */

//exports.Preferences = Preferences;
