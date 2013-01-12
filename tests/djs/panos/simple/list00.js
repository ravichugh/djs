// TODO : parametric lists
//


var print = function() /*: () / () -> Top / same  */ {};
//var assert = function() /*: () / () -> Top / same  */ {};

/*: (~lListNode : tyListNode > lListProto) */ "#weak";

/*: #define tyListNode
    {Dict|(and (dom v {"hd","tl"})
               (Int (sel v "hd"))
               ((sel v "tl")  :: Ref(~lListNode)))} */ "#define";

function List(head, tail)
/*: new [;Lthis]
        (this:Ref(Lthis), head:Int, tail:Ref(~lListNode))
      / (Lthis : d: Empty > lListProto, ~lListNode : frzn)
     -> Ref(~lListNode) / (~lListNode : same) */
{
  this.hd = head;
  this.tl = tail;
  var self = this;
  /*: self (~lListNode, frzn) */ "#freeze";
  return self;
};


//NOTE : We don't we need to thaw here cause the result is valid for all
//possible instantiations of the weak location
var listSum = function recurse(list)
/*: (list: Ref(~lListNode)) / (~lListNode: frzn) -> Int  / same */
{
  if (list != null) {
    var s1 = 0;
    var rest = list.tl;
    var s2 = recurse(rest);
    return (s1 + s2);
  }
  else {
    return 0;
  }
};

////NOTE : Ref(~l?) means that list is either null or points to a location
//~lListNode
//       
var listSumPos = function recurse(list)
/*: (list: Ref(~lListNode?)) / (~lListNode: frzn) -> { Int | (>= v 0)} / same */
{
  if (list != null) {
    assert(/*: {(not (= v null)) } */ list);
    var s1 = 0;
    /*: list lList1 */ "#thaw";
    if (list.hd > 0) {
      assert(/*: {(> v 0)} */ (list.hd)); //XXX : I need to thaw to establish this !!!
      s1 += list.hd;
    }
    /*: list (~lListNode, thwd lList1) */ "#freeze";
    assert(/*: Int */ (s1));
    var rest = list.tl;
    var s2 = recurse(rest);
    var result = s1 + s2;
    return result;
  }
  else {
    return 0;
  }
};

//NOTE: if we want to change the heap that is refered to by a formal parameter
//we need to use this notation ([sameType]) after the type for the structure we
//pass as a parameter.

var arrayToList = function(arr) 
/*: [;Larr;] (arr: Ref(Larr)) / (Larr: arr0: {Arr(Int) | (packed v)} [sameExact] > lArrPro) 
      -> Ref(~lListNode) / (Larr: sameExact) */
  //Weak locations are frozen by default

//sameType in the array annotation just says that we have a packed array of ints
//later in the loop, but it does not guarantee that we are talking about the
//same exactly array arr0. This needs to be specified by sameExact.
{
  var n = arr.length;
  var list /*: Ref(~lListNode) */ = null;
  
//At this point heap contains a value arr0 for the array arr.
//This is irrelevant to the array that we are going to use in the definition of
//the function type for the loop. So if we were to reference the specific
//array, we must specify it as an invariant, e.g. (= v arr0)


  for (var i /*: {Int | (>= v 0)} */ = 0; i < arr.length; i++) {
    var elt = arr[i];
    list = new List(elt, list);
  }
  return list;
};
//////////////


//var l1 = arrayToList([1,2,4,1,2,3,4,5,3,4,5]);
//printList(l1);
//print(listSumPos(l1));

