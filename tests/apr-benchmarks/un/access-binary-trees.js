
function TreeNode(left,right,item) {
  this.left = left;
  this.right = right;
  this.item = item;
  return this;
};

var tree1 = new TreeNode(null, null, 10);
var tree2 = new TreeNode(null, null, 20);
var tree3 = new TreeNode(tree1, tree2, 30);

var i = tree1.item;

i;

TreeNode.prototype.itemCheck = function(){
   if (this.left==null) return this.item;
   else return this.item + this.left.itemCheck() - this.right.itemCheck();
}


var ic = tree1.itemCheck;

ic;
ic.apply(tree1));

function bottomUpTree(item,depth){
   if (depth>0){
      return new TreeNode(
          bottomUpTree(2*item-1, depth-1)
         ,bottomUpTree(2*item, depth-1)
         ,item
      );
   }
   else {
      return new TreeNode(null,null,item);
   }
}


var tree4 = bottomUpTree(0,42);
ic = tree4.itemCheck;

ic;
ic.apply(tree4));

