
var fire = function (e) 
//Works when removing the second line of the type
/*: {(and
    (v :: (e: Str) -> Top)
    (v :: (e: Ref) / (e: {f: Str} > lObjPro) -> Top / sameType)
    )} */
{
  if (typeof e === 'string') {
    assert(/*: Str */ (e));
  }
  else if (typeof e === 'object') {
    //assert(false);
    assert(/*: Str */ (e.f));
  }
};

