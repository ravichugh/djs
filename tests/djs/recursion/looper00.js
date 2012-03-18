
/*: [~lLooper |-> ({Dict|((sel v "loop") :: tyLoop)}, lObjectProto)] */ "#weak";

var foo = function loop() /*: tyLoop */ {
  var self = this;
  self = /*: l */ "#thaw";
  var bar = self.loop;
  self = /*: (~lLooper, thwd l) */ "#freeze";
  return 1 + /*:apply*/ bar(self);
};

/*: #define tyLoop
    [[this:Ref(~lLooper)]] / [~lLooper |-> frzn] -> Int / same */ "#define";

var x = {"loop": foo};

x = /*: (~lLooper, frzn) */ "#freeze";

assert (/*: Int */ (/*:apply*/ foo(x)));

////////////////////////////////////////////////////////////////////////////////

x = /*: lThwd */ "#thaw";

var xloop = x.loop;

x = /*: (~lLooper, thwd lThwd) */ "#freeze";

assert (/*: Int */ (/*:apply*/ xloop(x)));

