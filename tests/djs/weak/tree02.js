
/*: (~lTreeNode |-> tyTreeNode > lTreeNodeProto) */ "#weak";

/*: #define tyTreeNode
    {Dict|(and (dom v {"item","left","right"})
               (Int (sel v "item"))
               ((sel v "left")  :: Ref(~lTreeNode))
               ((sel v "right") :: Ref(~lTreeNode)))} */ "#define";

/*: #define ctorTreeNode
        [;Lthis]
        (this:Ref(Lthis), left:Ref(~lTreeNode), right:Ref(~lTreeNode), item:Int)
      / (Lthis |-> d:Empty > lTreeNodeProto, ~lTreeNode |-> frzn)
     -> Ref(~lTreeNode) / (~lTreeNode |-> same) */ "#define";

function TreeNode(left,right,item) /*: new ctorTreeNode */ {
  this.left = left;
  this.right = right;
  this.item = item;

  var self = this;
  /*: self (~lTreeNode, frzn) */ "#freeze";
  return self;
};

////////////////////////////////////////////////////////////////////////////////

///// original function:
///// 
/////   function bottomUpTree(item,depth){
/////      if (depth>0){
/////         return new TreeNode(
/////             bottomUpTree(2*item-1, depth-1)
/////            ,bottomUpTree(2*item, depth-1)
/////            ,item
/////         );
/////      }
/////      else {
/////         return new TreeNode(null,null,item);
/////      }
/////   }

/*: #define tyBottomUpTree
       (item:Int, depth:Int)
     / (~lTreeNode |-> frzn,
        &TreeNode |-> _:Ref(lTreeNodeObj),
        lTreeNodeObj |-> _:{Dict|
           (and ((sel v "code") :: ctorTreeNode)
                ((sel v "prototype") :: Ref(lTreeNodeProto)))} > lFunPro,
        lTreeNodeProto |-> _:Dict > lObjPro)
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

////////////////////////////////////////////////////////////////////////////////

/*: #define tyItemCheck
    (this:Ref(~lTreeNode)) / (~lTreeNode |-> frzn) -> Int / same */ "#define";

// see tree01.js
var itemCheck = /*: tyItemCheck */ "#extern";
TreeNode.prototype.itemCheck = itemCheck;

////////////////////////////////////////////////////////////////////////////////

var tree = bottomUpTree(0,42);
/*: tree lThwd1 */ "#thaw";
var ic = tree.itemCheck;
/*: tree (~lTreeNode, thwd lThwd1) */ "#freeze";

assert (/*: tyItemCheck*/ ic);
assert (/*: Int */ (ic.apply(tree)));

