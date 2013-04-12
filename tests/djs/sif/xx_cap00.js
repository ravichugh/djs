/*****************************************************
 *
 * 
 * Simplified version of the [ECOOP'12] leak example.
 *
 *
 *****************************************************/


/*****************************************************
 *
 *
 * DJS definitions
 *
 *
 *****************************************************/

/*: "tests/djs/sif/__mozilla.dref" */ "#use";


// DJS DEFINITIONS BEGIN
var require = 
  /*: [;L;] ({Str|(= v "chrome")}) / () -> Ref(L) / 
  (L: { Cc: Ref(~lComponents_classes), 
        Ci: Ref(~lComponents_interfaces)} > lObjPro) */ "#extern";


var exports = /*: Ref(~extern) */ "#extern";

var testPriv = function(o) /*: [;L;] (Ref(L)) / (L: {Dict|(isPrivileged v)} > lObjPro) -> Top / sameType */ {};




/*****************************************************
 *
 *
 * Information flow properties
 *
 *
 *****************************************************/

//For every dictionary d:
//  All fields in d are public ==> d is public

/*: (forall (d) 
      (implies 
        (forall (f) (and (has d f) (public (sel d f))))
        (public d)
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

//XXX: will need something like this:
// /*: (forall (d) (implies (public d) (public (Ref(d)))) */ "#assume";


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
        (has v "_branches") ((sel v "_branches"):: Ref(~branches))
        (has v "_caches")   ((sel v "_caches"):: Ref(~caches))
        (implies (has v "getBranch") ((sel v "getBranch"):: (Str) -> Top))
        */ "#define";

/*: publicPrefFields 
        (has v "_branches") ((sel v "_branches"):: Ref(~publicBranches))
        (has v "_caches")   ((sel v "_caches"):: Ref(~publicCaches))
        (implies (has v "getBranch") ((sel v "getBranch"):: (Str) -> Top))
        */ "#define";

/*: (~dict: { } > lObjPro) */ "#weak";

var makePublicEmpty = /*: [;L;] () / () -> Ref(L) / (L: {Dict|(public v)} > lObjPro) */ "#extern";



/*****************************************************
 * Branches
 * **************************************************/

/*: (~publicBranches: {Dict|(public v)} > lObjPro) */ "#weak";

/*: (~branches: { } > lObjPro) */ "#weak";

var branches = /*: [;lB;] */ makePublicEmpty();
/*: branches (~publicBranches, frzn) */ "#freeze";


/*****************************************************
 * Caches
 * **************************************************/

/*: (~publicCaches: {Dict|(public v)} > lObjPro) */ "#weak";

/*: (~caches: { } > lObjPro) */ "#weak";

var caches = /*: [;lB;] */ makePublicEmpty();
/*: caches (~publicCaches, frzn) */ "#freeze";


/*****************************************************
 * Preferences
 * **************************************************/

/*: (~pref:       { Dict | (and prefFields)    } > lObjPro) */ "#weak";

/*: (~publicPref: { Dict | (and publicPrefFields) } > lObjPro) */ "#weak";

var preferences = {
    _branches: branches,
    _caches: caches
  };

/*: preferences (~publicPref, frzn) */ "#freeze";

//assert(/*: {(public v)} */ (preferences));


/**
 *
 * XXX: capability leaks only through assignment of secret valeus to global 
 * variable "Preferences". So we need the side effect - output heap annotations 
 * to denote that.
 * E.g. to prove the absense of capability leaks, for every location in output heap 
 * we should be able to prove: public v
 *
 */
//var func = function (name) /*: (Str) / (&preferences: Ref(~pref))-> Top / (&preferences: Ref(~public_pref)) */ {
  var name = /*: {Str|(public v)} */ "#extern";

  var branch = Cc["mozilla_org__preferences_service_1"].getService(Ci.nsIPrefService).getBranch(name);


  assert(/*: { Ref(~nsIPrefBranch) | TRU } */ (branch));
  
  /*: preferences lPreferences */ "#thaw";

  assert(/*: Ref(~publicBranches) */ (preferences._branches));

  var pb = preferences._branches;
  /*: pb lPrefBranches */ "#thaw";

  pb[name] = branch;

  assert(/*: Ref(~nsIPrefBranch) */ (pb[name]));

  /*: pb (~branches, frzn) */ "#freeze";

//  /*: pb (~branches, thwd lPrefBranches) */ "#freeze";
    
//  assert(/*: Ref(~privbranches) */ (pb));
//  //XXX: had to add this...
//  preferences._branches = pb;
//  assert(/*: Ref(~privbranches) */ (preferences._branches));
//
//  /*: preferences (~public_pref, frzn) */ "#freeze";
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
