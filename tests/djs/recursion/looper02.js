
/*: [~lLooper |-> (Empty, lLooperProto)] */ "#weak";

function Looper() /*:
  new [;Lnew]
      [[this:Ref(Lnew)]] / [~lLooper |-> frzn, Lnew |-> (_:Empty, lLooperProto)]
   -> Ref(~lLooper) / [~lLooper |-> same]
*/
{
  var self = this;
  /*: self (~lLooper, frzn) */ "#freeze";
  return self;
};

Looper.prototype.loop = function loop() /*: tyLoop */ {
  return 1 + loop.apply(this);
};

/*: #define tyLoop
    [[this:Ref(~lLooper)]] / [~lLooper |-> frzn] -> Int / same */ "#define";

////////////////////////////////////////////////////////////////////////////////

// the following is:    var x = new Looper();
//                      x.loop();

var x = new /*: [;lx;] lLooperProto */ Looper();
/*: x lThawX */ "#thaw";
var xloop = x.loop;
/*: x (~lLooper, thwd lThawX) */ "#freeze";
xloop.apply(x);
