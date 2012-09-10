
/*: (~lTreeNode |-> tyTreeNode > lTreeNodeProto) */ "#weak";

/*: #define tyTreeNode
    {Dict|(and (dom v {"item","left","right"})
               (Int (sel v "item"))
               ((sel v "left")  :: Ref(~lTreeNode))
               ((sel v "right") :: Ref(~lTreeNode)))} */ "#define";

function TreeNode(left,right,item)
/*: new [;Lthis]
        (this:Ref(Lthis), left:Ref(~lTreeNode), right:Ref(~lTreeNode), item:Int)
      / (Lthis |-> d:Empty > lTreeNodeProto, ~lTreeNode |-> frzn)
     -> Ref(~lTreeNode) / (~lTreeNode |-> same) */ {
  this.left = left;
  this.right = right;
  this.item = item;

  var self = this;
  /*: self (~lTreeNode,frzn) */ "#freeze";
  return self;
};

////////////////////////////////////////////////////////////////////////////////

var tree1 = new (/*: [;lTree1;] lTreeNodeProto */ TreeNode)(null, null, 10);
var tree2 = new (/*: [;lTree2;] lTreeNodeProto */ TreeNode)(null, null, 20);
var tree3 = new (/*: [;lTree2;] lTreeNodeProto */ TreeNode)(tree1, tree2, 30);

/*: tree1 lThwd1 */ "#thaw";

var i = tree1.item;

assert (/*: Int */ i);
