var read = function (x)
  /*: (x:Ref) / (x: d:Dict > x.pro)
   -> {(= v (objsel d "f" cur x.pro))} / sameExact */
{
  return x.f;
};
