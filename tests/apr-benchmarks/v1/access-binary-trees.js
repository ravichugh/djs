
/*: [~lTreeNode |-> (tyTreeNode, lTreeNodeProto)] */ "#weak";

/*: #define tyTreeNode
    {Dict|(and (dom v {"item","left","right"})
               ((sel v "item"):Int)
               ((sel v "left"):Ref(~lTreeNode))
               ((sel v "right"):Ref(~lTreeNode)))} */ "#define";

/*: #define ctorTreeNode
        [;Lthis]
        [[this:Ref(Lthis), left:Ref(~lTreeNode), right:Ref(~lTreeNode), item:Int]]
      / [Lthis |-> (d:Empty, lTreeNodeProto), ~lTreeNode |-> frzn]
     -> Ref(~lTreeNode) / [~lTreeNode |-> same] */ "#define";

function TreeNode(left,right,item) /*: new ctorTreeNode */ {
  this.left = left;
  this.right = right;
  this.item = item;

  /*: this (~lTreeNode, frzn) */ "#freeze";
  return this;
};


var tree1 = new (/*: [;lTree1;] lTreeNodeProto */ TreeNode)(null, null, 10);
var tree2 = new (/*: [;lTree2;] lTreeNodeProto */ TreeNode)(null, null, 20);
var tree3 = new (/*: [;lTree2;] lTreeNodeProto */ TreeNode)(tree1, tree2, 30);

/*: tree1 lThwd1 */ "#thaw";
var i = tree1.item;
/*: tree1 (~lTreeNode, thwd lThwd1) */ "#freeze";

assert (/*: Int */ i);


/*: #define tyItemCheck
    [[this:Ref(~lTreeNode)]] / [~lTreeNode |-> frzn] -> Int / same */ "#define";

TreeNode.prototype.itemCheck = function itemCheck() /*: tyItemCheck */ {
  var i;
  /*: this lThis1 */ "#thaw";
  var b = this.left == null;
  /*: this (~lTreeNode, thwd lThis1) */ "#freeze";

  if (b) {
    /*: this lThis2 */ "#thaw";
    i = this.item;
    /*: this (~lTreeNode, thwd lThis2) */ "#freeze";
    return i;
  }
  else {
    /*: this lThis3 */ "#thaw";
    i = this.item;
    var left = this.left;
    var right = this.right;
    /*: this (~lTreeNode, thwd lThis3) */ "#freeze";
    return i + itemCheck.apply(left) + itemCheck.apply(right);
  }
};


/*: tree1 lThwd2 */ "#thaw";
var ic = tree1.itemCheck;
/*: tree1 (~lTreeNode, thwd lThwd2) */ "#freeze";

assert (/*: tyItemCheck */ ic);
assert (/*: Int */ (ic.apply(tree1)));


/*: #define tyBottomUpTree
       [[item:Int, depth:Int]]
     / [~lTreeNode |-> frzn,
        &TreeNode |-> _:Ref(lTreeNodeObj),
        lTreeNodeObj |-> (_:{Dict|
           (and ((sel v "code") : ctorTreeNode)
                ((sel v "prototype") : Ref(lTreeNodeProto)))}, lFunctionProto),
        lTreeNodeProto |-> (_:Dict, lObjectProto)]
    -> Ref(~lTreeNode) / same */ "#define";

var bottomUpTree = function foo(item,depth) /*: tyBottomUpTree */ {
  if (depth > 0) {
    return new /*: [;lNew1] lTreeNodeProto */ TreeNode(
      foo (2*item-1, depth-1),
      foo (2*item, depth-1),
      item
    );
  }
  else {
    return new /*: [;lNew2] lTreeNodeProto */ TreeNode(null,null,item);
  }
};


var tree4 = bottomUpTree(0,42);
/*: tree4 lThwd4 */ "#thaw";
ic = tree4.itemCheck;
/*: tree4 (~lTreeNode, thwd lThwd4) */ "#freeze";

assert (/*: tyItemCheck*/ ic);
assert (/*: Int */ (ic.apply(tree4)));

