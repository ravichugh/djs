/*: [~lTreeNode |-> (tyTreeNode, lTreeNodeProto)] */ "#weak";

/*: #define tyTreeNode
    {Dict|(and (dom v {"item","left","right"})
               ((sel v "item"):Int)
               ((sel v "left"):Ref(~lTreeNode))
               ((sel v "right"):Ref(~lTreeNode)))} */ "#define";

/*: #define tyItemCheck [[this:Ref(~lTreeNode)]] -> Int */ "#define";

var blah = {};
blah.itemCheck = function f() /*: tyItemCheck */ {
  if (this.left == null) { return this.item; }
  else { return this.item + f.apply(this.left) + f.apply(this.right); }
};
