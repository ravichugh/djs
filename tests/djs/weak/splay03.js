
/*: #define tyNode
    {(and (= (tag v) "Dict")
          (Int (sel v "key"))
          (Str (sel v "value"))
          (implies (has v "left")  ((sel v "left")  :: Ref(~lNode)))
          (implies (has v "right") ((sel v "right") :: Ref(~lNode))))}
*/ "#define";

/*: (~lNode |-> tyNode > lNodeProto) */ "#weak";

function Node(key, value)
 /*: new [;Lnew]
     (this:Ref(Lnew), key:Int, value:Str)
   / (Lnew |-> _:Empty > lNodeProto, ~lNode |-> frzn)
  -> Ref(~lNode) / (~lNode |-> same) */
{
  this.key = key;
  this.value = value;

  var self = this;
  /*: self (~lNode, frzn) */ "#freeze";
  return self;
};

var SplayTree = {Node: Node};

SplayTree.Node.prototype.left = null;

SplayTree.Node.prototype.right = null;

////////////////////////////////////////////////////////////////////////////////

/*: #define leftAndRight
    {Dict|(and ((sel v "left") :: Ref(~lNode))
               ((sel v "right") :: Ref(~lNode)))} */ "#define";

// not writing (= (sel v "left") null) in this macro, because then when
// doing a read, would get either v::Ref(~lNode) or v::Null, which does _not_
// imply v::Ref(~lNode) without doing CanFlow. so, basically doing the
// upcast explicitly here.

// this version, unlike the original, just visits each node, rather than
// applying a function f at each node

SplayTree.Node.prototype.traverse_ = function traverse_()
/*: (this:Ref(~lNode))
  / (~lNode |-> frzn, lNodeProto |-> _:leftAndRight > lObjPro)
 -> Top / same */
{
  // to support the original version       while(current)
  // need to add thaw/freeze around
  // the guard. in the meantime, using
  // a temporary variable b.

  var current = this;

  /*: current lThaw1 */ "#thaw";
  var b = current;
  /*: current (~lNode, thwd lThaw1) */ "#freeze"; 

  /*: (&b |-> _:Top, &current |-> _:Ref(~lNode), ~lNode |-> frzn,
       lNodeProto |-> _:leftAndRight > lObjPr)
   -> (&b |-> _:Top, &current |-> _:Ref(~lNode), ~lNode |-> frzn,
       lNodeProto |-> same) */
  while (b) {

    /*: current lThaw2 */ "#thaw";
    var left = current.left;
    /*: current (~lNode, thwd lThaw2) */ "#freeze";

    if (left) traverse_.apply(left);

    /*: current lThaw3 */ "#thaw";
    var right = current.right;
    /*: current (~lNode, thwd lThaw3) */ "#freeze";

    b = current;
  }
};
