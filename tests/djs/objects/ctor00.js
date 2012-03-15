function F()
/*: ctor [;L;]
    [[this:Ref(L)]]
  / [L |-> (dThis:{(= v empty)}, &F_proto), &F_proto |-> (_:Top, lObjectProto)]
 -> Ref(L)
  / [L |-> (_:{(= v (upd dThis "f" 1))}, &F_proto), &F_proto |-> same] */
{
  this.f = 1;
  return this;
}
