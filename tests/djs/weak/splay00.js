
/*: #define tyNode
    {Dict|(and (dom v {"key","value"})
               ((sel v "key")   : Int)
               ((sel v "value") : Str))} */ "#define";

/*: [~lNode |-> (tyNode, lNodeProto)] */ "#weak";

function Node(key, value) /*: new [;Lnew]
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

var node1 = new /*: [;lNew1] lNodeProto */ Node(0, "0");

/*: node1 lThaw1 */ "#thaw";

assert (/*: Int */ (node1.key));
assert (/*: Str */ (node1.value));
assert (/*: Null */ (node1.left));
assert (/*: Ref(~lNode) */ (node1.left));

