/*: [~lTreeNode |-> (tyTreeNode, lTreeNodeProto)] */ "#weak";

/*: #define tyTreeNode
    {Dict|(and (dom v {"item","left","right"})
               ((sel v "item"):Int)
               ((sel v "left"):Ref(~lTreeNode))
               ((sel v "right"):Ref(~lTreeNode)))} */ "#define";

/*: #define tyg
    [[obj:Ref(~lTreeNode)]] -> Int */ "#define";

var g = function(obj) /*: tyReadLeftRight */ {
  // TODO this would require tracking more syntactically
  return obj.item + obj.left.item;
};
