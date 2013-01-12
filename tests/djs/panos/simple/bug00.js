var bug = function(l) 
/*: [;L;] (l:Ref(L?)) / (L: Top) -> Top / same */
{
  if (l != null) {
    return 1;
  }
  assert(/*: {FLS} */ 1);
  return 0;
};

//var a = {"1":1};
//print(bug(a));
//var b = null;
//print(bug(b));
