
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
     -> Ref(~lTreeNode) / (~lTreeNode |-> same) */
{
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
/////   TreeNode.prototype.itemCheck = function(){
/////      if (this.left==null) return this.item;
/////      else return this.item + this.left.itemCheck() - this.right.itemCheck();
/////   }
/////

/*: #define tyItemCheck
    (this:Ref(~lTreeNode)) / (~lTreeNode |-> frzn) -> Int / same */ "#define";

TreeNode.prototype.itemCheck = function itemCheck() /*: tyItemCheck */ {
  var i;
  var self = this;
  /*: self lSelf1 */ "#thaw";
  var b = self.left == null;
  /*: self (~lTreeNode, thwd lSelf1) */ "#freeze";

  if (b) {
    /*: self lSelf2 */ "#thaw";
    i = self.item;
    /*: self (~lTreeNode, thwd lSelf2) */ "#freeze";
    return i;
  }
  else {
    /*: self lSelf3 */ "#thaw";
    i = self.item;
    var left = self.left;
    var right = self.right;
    /*: self (~lTreeNode, thwd lSelf3) */ "#freeze";
    return i + itemCheck.apply(left) + itemCheck.apply(right);
  }
};

////////////////////////////////////////////////////////////////////////////////

var tree1 = new (/*: lTree1 > lTreeNodeProto */ TreeNode)(null, null, 10);

/*: tree1 lThwd1 */ "#thaw";
var ic = tree1.itemCheck;
/*: tree1 (~lTreeNode, thwd lThwd1) */ "#freeze";

assert (/*: tyItemCheck */ ic);
assert (/*: Int */ (ic.apply(tree1)));

