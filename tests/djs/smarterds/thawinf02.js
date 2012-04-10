/*: [~lTreeNode |-> (tyTreeNode, lTreeNodeProto)] */ "#weak";

/*: #define tyTreeNode
    {Dict|(and (dom v {"item","left","right"})
               ((sel v "item"):Int)
               ((sel v "left"):Ref(~lTreeNode))
               ((sel v "right"):Ref(~lTreeNode)))} */ "#define";

/*: #define tyItemCheck
    [[obj:Ref(~lTreeNode)]] / [~lTreeNode |-> frzn] -> Int / same */ "#define";

var blah = {};
blah.itemCheck = function f(obj) /*: tyItemCheck */ {
  if (obj.left == null) { return obj.item; }
  else { return obj.item + f.apply(obj.left) + f.apply(obj.right); }
};
