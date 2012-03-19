
/*: [~lLooper |-> (tyLooper, lLooperProto)] */ "#weak";

function Looper() /*:
  new [;Lnew]
      [[this:Ref(Lnew)]]
    / [~lLooper |-> frzn, Lnew |-> (_:Empty, lLooperProto) ]
   -> Ref(~lLooper) / [~lLooper |-> same]
*/
{
  this.loop = function loop() /*: tyLoop */ {
    var self = this;
    /*: self l */ "#thaw";
    var bar = self.loop;
    /*: self (~lLooper, thwd l) */ "#freeze";
    return 1 + bar.apply(self);
  };

  var self = this;
  /*: self (~lLooper, frzn) */ "#freeze";
  return self;
};

/*: #define tyLoop
    [[this:Ref(~lLooper)]] / [~lLooper |-> frzn] -> Int / same */ "#define";

/*: #define tyLooper {Dict|((sel v "loop") :: tyLoop)} */ "#define";

var x = new /*: [;lx] lLooperProto */ Looper();
/*: x lThaw */ "#thaw";
var foo = x.loop;
/*: x (~lLooper, thwd lThaw) */ "#freeze";
assert (/*: Int */ (foo.apply(x)));
