var bug = function(l) /*: [;L;] (l:Ref(L)) / (L: Top) -> Int / same */
{
  if (l != null) {
    return 1;
  }
  assert(/*: {FLS} */ 1);
  return 0;
};
