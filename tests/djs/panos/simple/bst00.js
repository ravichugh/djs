//GOAL: encode the property of a Binary Search Tree in the DJS logic using weak
//references. (Can this be done?)

///////// Print functions
var bstreeToString = function(tree) {
  if (tree != null) {
    var left = tree.left;
    var right = tree.right;
    var item = tree.item; 
    return subTreeToString(left,right,item);
  }
  else {
    return "_";
  }
};

var subTreeToString = function(t1, t2, item) {
  return (bstreeToString(t1) + " " + item + bstreeToString(t2));
}
////////////////

function Node(left, right, item) {
  this.left = left;
  this.right = right;
  this.item = item;
};


var addBSTNode = function(tree, item) {
  if (tree != null) {
    var left = tree.left;
    var right = tree.right;
    var rootItem = tree.item;
    //print("Adding "+ item +" @ " + rootItem);
//We're not gonna check if the item part of the tree node is null cause the
//tyTreeNode guarantees that it's not and in fact is an integer.
    if (rootItem > item) {
      var newLeft = addBSTNode(left, item);
      return new Node(newLeft, right, rootItem);
    }
    else {
      var newRight = addBSTNode(right, item);
      return new Node(left, newRight, rootItem);
    }
  }
  else {
    tree = new Node(null, null, item);
    return tree;
  }
};


var tree0 = addBSTNode(null, 0);
var tree1 = addBSTNode(tree0, 1);
var tree2 = addBSTNode(tree1, 2);
var tree3 = addBSTNode(tree2, 3);
var tree4 = addBSTNode(tree3, 4);
var tree5 = addBSTNode(tree4, 5);
var tree6 = addBSTNode(tree5, 6);
var tree7 = addBSTNode(tree6, 10);
var tree8 = addBSTNode(tree7, 9);
var tree9 = addBSTNode(tree8, 8);
var tree10 = addBSTNode(tree9, 7);
var tree11 = addBSTNode(tree10, 6);

//print(bstreeToString(tree0));
//print(bstreeToString(tree1));
//print(bstreeToString(tree2));
//print(bstreeToString(tree3));
//print(bstreeToString(tree4));
//print(bstreeToString(tree5));
print(bstreeToString(tree11));
