/*: (~lTreeNode:
       {Dict|(and (dom v {"item","left","right"}) (Int (sel v "item"))
                  ((sel v "left") :: Ref(~lTreeNode))
                  ((sel v "right") :: Ref(~lTreeNode)))} > lTreeNodeProto) */ "#weak";

function TreeNode(left,right,item)
/*:   (this:Ref, left:Ref(~lTreeNode), right:Ref(~lTreeNode), item:Int)
    / (this: d:Empty > lTreeNodeProto) -> Ref(~lTreeNode) / () */ {
  this.left = left;
  this.right = right;
  this.item = item;

  /*: this (~lTreeNode, frzn) */ "#freeze";
  return this;
};

var tree1 = new TreeNode(null, null, 10);
var tree2 = new TreeNode(null, null, 20);
var tree3 = new TreeNode(tree1, tree2, 30);

var i = tree1.item;
assert (typeof i === "number");

TreeNode.prototype.itemCheck = function itemCheck() /*: (this:Ref(~lTreeNode)) -> Int */ {
  if (this.left == null) { return this.item; }
  else { return this.item + itemCheck.apply(this.left) + itemCheck.apply(this.right); }
};

var j = (tree1.itemCheck).apply(tree1);
assert (typeof j === "number");

var bottomUpTree = function foo(item,depth) /*: (item:Int, depth:Int) -> Ref(~lTreeNode) */ {
  if (depth > 0) {
    return new TreeNode(
      foo (2*item-1, depth-1),
      foo (2*item, depth-1),
      item
    );
  }
  else {
    return new TreeNode(null,null,item);
  }
};

var tree4 = bottomUpTree(0,42);
var k = (tree4.itemCheck).apply(tree4);
assert (typeof k === "number");
