
/*: #define tyNode
    {(and (= (tag v) "Dict") ((sel v "key") : Int) ((sel v "value") : Str)
          (implies (has v "left")  ((sel v "left")  : Ref(~lNode)))
          (implies (has v "right") ((sel v "right") : Ref(~lNode))))}
*/ "#define";

/*: [~lNode |-> (tyNode, lNodeProto)] */ "#weak";

function Node(key, value) /*: new [;Lnew]
     [[this:Ref(Lnew), key:Int, value:Str]] / [Lnew |-> (_:Empty, lNodeProto)]
  -> Ref(~lNode) / [] */
{
  this.key = key;
  this.value = value;

  /*: this (~lNode, frzn) */ "#freeze";
  return this;
};

var SplayTree = {Node: Node};

SplayTree.Node.prototype.left = null;

SplayTree.Node.prototype.right = null;

/*: #define leftAndRight
    {Dict|(and ((sel v "left") :: Ref(~lNode))
               ((sel v "right") :: Ref(~lNode)))} */ "#define";

SplayTree.Node.prototype.traverse_ = function traverse_()
/*: [[this:Ref(~lNode)]] / [lNodeProto |-> (_:leftAndRight , lObjectProto)]
 -> Top / sameType */
{
  var current = this;
  var b = current;
  /*: [&b |-> _:Top, &current |-> _:Ref(~lNode), lNodeProto |-> (_:leftAndRight, lObjectProto)]
   -> sameType */
  while (b) {
    var left = current.left;
    if (left) traverse_.apply(left);
    var right = current.right;
    b = current;
  }
};
