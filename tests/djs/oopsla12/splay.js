
/*: tyNode {Dict|(and (Int (sel v "key")) (Str (sel v "value"))
                 (implies (has v "left")  ((sel v "left")  :: Ref(~lNode)))
                 (implies (has v "right") ((sel v "right") :: Ref(~lNode))))} */ "#define";

/*: (~lNode: tyNode > lNodeProto) */ "#weak";

function Node(key, value) /*: new (this:Ref, key:Int, value:Str)
                                / (this: Empty > lNodeProto) -> Ref(~lNode) / () */ {
  this.key = key;
  this.value = value;
  /*: this (~lNode, frzn) */ "#freeze";
  return this;
};

var SplayTree = {Node: Node};

SplayTree.Node.prototype.left = null;

SplayTree.Node.prototype.right = null;

/*: leftAndRight {left: Ref(~lNode), right:Ref(~lNode)} */ "#define";

Node.prototype.traverse_ = function traverse_()
/*: (this:Ref(~lNode)) / (lNodeProto: leftAndRight [sameExact] > lObjPro) -> Top / same */ {
  var current = this;
  var b /*: Top */ = current; // TODO get rid of b temporary
  while (b) {
    var left = current.left;
    if (left) traverse_.apply(left);
    b = current.right;
  }
};

