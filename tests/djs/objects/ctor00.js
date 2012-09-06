function F()
/*: new [;L;]
    (this:Ref(L))
  / (L |-> dThis:{(= v empty)} > &FProto, &FProto |-> _:Top > lObjectProto)
 -> Ref(L)
  / (L |-> _:{(= v (upd dThis "f" 1))} > &FProto, &FProto |-> same) */
{
  this.f = 1;
  return this;
}
