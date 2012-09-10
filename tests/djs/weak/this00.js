
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

  /*: this (~lTreeNode,frzn) */ "#freeze";
  return this;
};
