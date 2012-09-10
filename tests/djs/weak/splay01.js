
/*: #define tyNode
    {(and (= (tag v) "Dict")
          (or (dom v {"key","value"}) (dom v {"key","value","left","right"}))
          (Int (sel v "key"))
          (Str (sel v "value"))
          (implies (has v "left")  ((sel v "left")  :: Ref(~lNode)))
          (implies (has v "right") ((sel v "right") :: Ref(~lNode))))}
*/ "#define";

/*: (~lNode |-> tyNode > lNodeProto) */ "#weak";

function Node(key, value) /*: new [;Lnew]
     (this:Ref(Lnew), key:Int, value:Str)
   / (Lnew |-> _:Empty > lNodeProto, ~lNode |-> frzn)
  -> Ref(~lNode) / (~lNode |-> same) */
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

////////////////////////////////////////////////////////////////////////////////

var node1 = new /*: [;lNew1] lNodeProto */ Node(1, "1");
var node2 = new /*: [;lNew2] lNodeProto */ Node(2, "1");
var node3 = new /*: [;lNew3] lNodeProto */ Node(3, "3");

/*: node1 lThaw1 */ "#thaw";

node1.left = node2;
node1.right = node3;

/*: node1 (~lNode, thwd lThaw1) */ "#freeze";

