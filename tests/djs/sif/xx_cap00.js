/**
 *
 * Simplified version of the [ECOOP'12] leak example.
 *
 */

/*: "tests/djs/sif/__mozilla.dref" */ "#use";


// DJS DEFINITIONS BEGIN
var require = 
  /*: [;L;] ({Str|(= v "chrome")}) / () -> Ref(L) / 
  (L: { Cc: Ref(~lComponents_classes), 
        Ci: Ref(~lComponents_interfaces)} > lObjPro) */ "#extern";


var exports = /*: Ref(~extern) */ "#extern";


// DJS DEFINITIONS END


// SECURITY PROPERTIES BEGIN

// /*: (implies (isPrivileged v) (isTainted v)) */ "#assume";

//If all fields in a dictionary are public then the dictionary is public itself
/*: (forall (d) 
      (implies 
        (forall (f) (and (has d f) (public (sel d f))))
        (isPrivileged d)
      )
    ) */ "#assume";


/// If a dictionary contains a privilieged binding then it's privileged itself
/*: (forall (d f)
        (implies (and (has d f) (isPrivileged (sel d f))) (isPrivileged d))
    ) */ "#assume";

//// All fields of a privileged dictionary are privileged
///*: (forall (d f)
//      (implies 
//        (isPrivileged d)
//        (implies (has d f) (isPrivileged (sel d f)))
//      )
//    ) */ "#assume";


var testPriv = function(o) /*: [;L;] (Ref(L)) / (L: {Dict|(isPrivileged v)} > lObjPro) -> Top / sameType */ {};

// SECURITY PROPERTIES END



/*****************************************************
 *
 *
 * Module code starts here
 *
 *
 *****************************************************/

  
///PV: Desuraging destructuring assignment:
///var {Cc, Ci} = require("chrome");
var a = (/*: [;l;] */ require)("chrome");

assert(/*: Ref(~lComponents_classes) */ (a.Cc));
assert(/*: Ref(~lComponents_interfaces) */ (a.Ci));

var Cc = a.Cc;
var Ci = a.Ci;



/*****************************************************
 * Definitions
 * **************************************************/

/*: prefFields 
        (dom v {"_branches", "_caches"})
        ((sel v "_branches"):: Ref(~branches))
        ((sel v "_caches"):: Ref(~caches))
        (implies (has v "getBranch") ((sel v "getBranch"):: (Str) -> Top))
        */ "#define";

/*: privPrefFields 
        (implies (has v "_branches")   ((sel v "_branches"):: Ref(~privbranches)))
        (implies (has v "_caches")   ((sel v "_caches"):: Ref(~caches)))
        (implies (has v "getBranch") ((sel v "getBranch"):: (Str) -> Top))
        */ "#define";

/*: (~dict: { } > lObjPro) */ "#weak";


var makePublicEmpty = /*: [;L;] () / () -> Ref(L) / (L: {Dict|(public v)} > lObjPro) */ "#extern";

/*****************************************************
 * Branches
 * **************************************************/

/*: (~branches: {Dict|(public v)} > lObjPro) */ "#weak";

/*: (~secret_branches: { } > lObjPro) */ "#weak";

var branches = /*: [;lB;] */ makePublicEmpty();
/*: branches (~branches, frzn) */ "#freeze";


/*****************************************************
 * Caches
 * **************************************************/

/*: (~caches: {Dict|(public v)} > lObjPro) */ "#weak";

/*: (~secret_caches: { } > lObjPro) */ "#weak";

var caches = /*: [;lB;] */ makePublicEmpty();
/*: caches (~caches, frzn) */ "#freeze";


/*****************************************************
 * Preferences
 * **************************************************/
/*: (~pref:     { Dict | (and prefFields)     } > lObjPro) */ "#weak";

/*: (~privpref: { Dict | (and privPrefFields) } > lObjPro) */ "#weak";

//var preferences = {
//    _branches: branches,
//    _caches: caches
//  };
//
///*: preferences (~pref, frzn) */ "#freeze";
//
//
//
///**
// *
// * XXX: capability leaks only through assignment of secret valeus to global 
// * variable "Preferences". So we need the side effect - output heap annotations 
// * to denote that.
// * E.g. to prove the absense of capability leaks, for every location in output heap 
// * we should be able to prove: safe v
// *
// */
////var func = function (name) /*: (Str) / (&preferences: Ref(~pref))-> Top / (&preferences: Ref(~privpref)) */ {
//  var name = /*: {Str|(safe v)} */ "#extern";
//
//  var branch = Cc["mozilla_org__preferences_service_1"].getService(Ci.nsIPrefService).getBranch(name);
//
//  assert(/*: Ref(~pref) */ (preferences));
//
//  assert(/*: {Ref(~nsIPrefBranch)|TRU} */ (branch));
//  assert(/*: {(isPrivileged v)} */ (branch));
//  
//  /*: preferences lPreferences */ "#thaw";
//
//  assert(/*: Ref(~branches) */ (preferences._branches));
//
//  var pb = preferences._branches;
//  /*: pb lPrefBranches */ "#thaw";
//
//  pb[name] = branch;
//
//  assert(/*: Ref(~nsIPrefBranch) */ (pb[name]));
//  assert(/*: {(isPrivileged v)} */ (pb[name]));
//
//  /*: pb (~privbranches, frzn) */ "#freeze";
//
////  /*: pb (~branches, thwd lPrefBranches) */ "#freeze";
//    
//  assert(/*: Ref(~privbranches) */ (pb));
//  //XXX: had to add this...
//  preferences._branches = pb;
//  assert(/*: Ref(~privbranches) */ (preferences._branches));
//
//  /*: preferences (~privpref, frzn) */ "#freeze";
//
//
////  assert(/*: {(isPrivileged v)} */ (preferences._branches));
////  assert(/*: {(isPrivileged v)} */ (preferences));
//
////};
//
////preferences.getBranch = func;
///* other properties */
//
////exports.preferences = preferences;
