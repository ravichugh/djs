
/*: [~lTreeNode |-> (frzn, tyTreeNode, lTreeNodeProto)] */ "#weak";

/*: #define tyTreeNode
    {Dict|(and ((sel v "item"):Int)
               ((sel v "left"):Ref(~lTreeNode))
               ((sel v "right"):Ref(~lTreeNode)))} */ "#define";

function TreeNode(left,right,item)
/*: new [;Lthis]
        [[this:Ref(Lthis), left:Ref(~lTreeNode), right:Ref(~lTreeNode), item:Int]]
      / [Lthis |-> (d:Empty, lTreeNodeProto),
        ~lTreeNode |-> (frzn, tyTreeNode, lTreeNodeProto)]
     -> Ref(~lTreeNode) / [~lTreeNode |-> same] */ {
  this.left = left;
  this.right = right;
  this.item = item;

  var self = this;
  self = /*: ~lTreeNode */ "#freeze";
  return self;
};

var tree = new (/*: [;l;] lTreeNodeProto */ TreeNode)(null, null, 10);

tree = /*: lThwd1 */ "#thaw";

var i = tree.item;

assert (/*: Int */ i);
