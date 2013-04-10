var {Cc, Ci} = require("chrome");

var Preferences = {
  branches: {},
  caches: {},
  getBranch: function (name) /*: (Str) -> Top */  {
    if (name in this. branches) return this. branches[name];
    let branch = Cc["@mozilla.org/preferences-service;1"]
      .getService(Ci.nsIPrefService).getBranch(name);
    /* other statements */
    return this. branches[name] = branch;
  }
  /* other properties */

};

exports.Preferences = Preferences;
