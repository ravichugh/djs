function F()
/*: new [;L;]
    [[this:Ref(L)]]
  / [L |-> (dThis:{(= v empty)}, &F_proto), &F_proto |-> (_:Dict, lObjectProto)]
 -> Ref(L)
  / [L |-> (_:{(= v (upd dThis "f" 1))}, &F_proto), &F_proto |-> same] */
{
  this.f = 1;
  return this;
}

/*: Ref(&F_proto) */ (F.prototype);

F.prototype.g = "sweet";

var x = new (/*: [;lx;] &F_proto */ F)();

/*: {(= v 1)} */ (x.f);
/*: {(= v "sweet")} */ (x.g);

F.prototype.g = "updated";

/*: {(= v "updated")} */ (x.g);
