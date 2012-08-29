
/*: [~lTreeNode |-> (tyTreeNode, lTreeNodeProto)] */ "#weak";

/*: #define tyTreeNode {Dict|(and
      (dom v {"item","left","right"}) ((sel v "item"):Int)
      ((sel v "left"):Ref(~lTreeNode)) ((sel v "right"):Ref(~lTreeNode)))} */ "#define";

/*: #define ctorTreeNode [;Lthis]
    [[this:Ref(Lthis), left:Ref(~lTreeNode), right:Ref(~lTreeNode), item:Int]]
  / [Lthis |-> (d:Empty, lTreeNodeProto), ~lTreeNode |-> frzn]
 -> Ref(~lTreeNode) / [~lTreeNode |-> frzn] */ "#define";

function TreeNode(left,right,item) /*: new ctorTreeNode */ {
  this.left = left;
  this.right = right;
  this.item = item;

  /*: this (~lTreeNode, frzn) */ "#freeze";
  return this;
};


var tree1 = new (/*: [;lTree1;] lTreeNodeProto */ TreeNode)(null, null, 10);
assert (/*: Ref(~lTreeNode) */ tree1);
var tree2 = new (/*: [;lTree2;] lTreeNodeProto */ TreeNode)(null, null, 20);
var tree3 = new (/*: [;lTree2;] lTreeNodeProto */ TreeNode)(tree1, tree2, 30);

var i = tree1.item;
assert (typeof i === "number");


/*: #define tyItemCheck [[this:Ref(~lTreeNode)]] -> Int */ "#define";

TreeNode.prototype.itemCheck = function itemCheck() /*: tyItemCheck */ {
  if (this.left == null) { return this.item; }
  else { return this.item + itemCheck.apply(this.left) + itemCheck.apply(this.right); }
};

var j = (tree1.itemCheck).apply(tree1);
assert (typeof j === "number");


/*: #define tyBottomUpTree
       [[item:Int, depth:Int]]
     / [~lTreeNode |-> frzn, &TreeNode |-> _:Ref(lTreeNodeObj),
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
assert (/*: Ref(~lTreeNode) */ tree4);
var k = (tree4.itemCheck).apply(tree4);
assert (typeof k === "number");

