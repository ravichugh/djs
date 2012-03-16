var x = /*: lx */ {};

x.loop = function _loop()
/*: [[this:Ref(lx)]]
  / [lx |-> (dx:{Dict|((sel v "_loop"):tyLoop)}, lObjectProto)]
 -> Int / same */
{
  return this._loop();
};

/*: #define tyLoop [[this:Ref(lx)]] -> Int */ "#define";

// definitions above type check...

///////////////////////////////////////////////////////////////////////////////

// ... but can't actually check any calls

var i = x.loop();
