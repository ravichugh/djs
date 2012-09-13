function F()
/*: new [;L;]
    (this:Ref(L))
  / (L |-> dThis:{(= v empty)} > lFProto, lFProto |-> _:Dict > lObjPro)
 -> Ref(L)
  / (L |-> _:{(= v (upd dThis "f" 1))} > lFProto, lFProto |-> same) */
{
  this.f = 1;
  return this;
}

assert (/*: Ref(lFProto) */ (F.prototype));

F.prototype.g = "sweet";

var x = new (/*: lx > lFProto */ F)();

assert (x.f == 1);
assert (x.g == "sweet");

F.prototype.g = "updated";

assert (x.g == "updated");
