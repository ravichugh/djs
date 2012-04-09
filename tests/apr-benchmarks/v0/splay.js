
/*: #define tyNode
    {(and (= (tag v) "Dict") ((sel v "key") : Int) ((sel v "value") : Str)
          (implies (has v "left")  ((sel v "left")  : Ref(~lNode)))
          (implies (has v "right") ((sel v "right") : Ref(~lNode))))}
*/ "#define";

/*: [~lNode |-> (tyNode, lNodeProto)] */ "#weak";

function Node(key, value)
 /*: new [;Lnew]
     [[this:Ref(Lnew), key:Int, value:Str]]
   / [Lnew |-> (_:Empty, lNodeProto), ~lNode |-> frzn]
  -> Ref(~lNode) / [~lNode |-> same] */
{
  this.key = key;
  this.value = value;

  var self = this;
  /*: self (~lNode, frzn) */ "#freeze";
  return self;
};

var SplayTree = {Node: Node};

SplayTree.Node.prototype.left = null;

SplayTree.Node.prototype.right = null;

/*: #define leftAndRight
    {Dict|(and ((sel v "left") :: Ref(~lNode))
               ((sel v "right") :: Ref(~lNode)))} */ "#define";

SplayTree.Node.prototype.traverse_ = function traverse_()
/*: [[this:Ref(~lNode)]] / [~lNode |-> frzn, lNodeProto |-> (_:leftAndRight , lObjectProto)]
 -> Top / same */
{
  var current = this;

  /*: current lThaw1 */ "#thaw";
  var b = current;
  /*: current (~lNode, thwd lThaw1) */ "#freeze"; 

  /*: [&b |-> _:Top, &current |-> _:Ref(~lNode), ~lNode |-> frzn,
       lNodeProto |-> (_:leftAndRight, lObjectProto)]
   -> [&b |-> _:Top, &current |-> _:Ref(~lNode), ~lNode |-> frzn,
       lNodeProto |-> same]*/
  while (b) {

    /*: current lThaw2 */ "#thaw";
    var left = current.left;
    /*: current (~lNode, thwd lThaw2) */ "#freeze";

    if (left) traverse_.apply(left);

    /*: current lThaw3 */ "#thaw";
    var right = current.right;
    /*: current (~lNode, thwd lThaw3) */ "#freeze";

    b = current;
  }
};
