var x = /*: lx */ {};

x.loop = function _loop() /*: tyLoop */ {
  return this._loop();
};

/*: #define tyLoop
    [[this:Ref(lx)]]
  / [lx |-> (_:{dx:Dict|(and ((sel dx "_loop"):tyLoopHelp))}, lObjectProto)]
 -> Int / same */ "#define";

/*: #define tyLoopHelp
    [[this:Ref(lx)]] / [lx |-> (_:{(= v dx)}, lObjectProto)]
 -> Int / same */ "#define";

assert (/*: tyLoop */ (x.loop));

x._loop = x.loop;

assert (/*: tyLoop */ (x._loop));

// the trick above allows the definitions above to type check...

///////////////////////////////////////////////////////////////////////////////

// ... but can't actually check any calls

var i = x.loop();
