function F()
/*: new [;L;]
    [[this:Ref(L)]]
  / [L |-> (dThis:{(= v empty)}, &FProto), &FProto |-> (_:Dict, lObjectProto)]
 -> Ref(L)
  / [L |-> (_:{(= v (upd dThis "f" 1))}, &FProto), &FProto |-> same] */
{
  this.f = 1;
  return this;
}

/*: Ref(&FProto) */ (F.prototype);

F.prototype.g = "sweet";

var x = new (/*: [;lx;] &FProto */ F)();

/*: {(= v 1)} */ (x.f);
/*: {(= v "sweet")} */ (x.g);

F.prototype.g = "updated";

/*: {(= v "updated")} */ (x.g);
