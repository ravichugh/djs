function F()
/*: new [;L;]
    (this:Ref(L))
  / (L |-> dThis:{(= v empty)} > lFProto, lFProto |-> _:Top > lObjectProto)
 -> Ref(L)
  / (L |-> _:{(= v (upd dThis "f" 1))} > lFProto, lFProto |-> same) */
{
  this.f = "not 1";
  return this;
}
