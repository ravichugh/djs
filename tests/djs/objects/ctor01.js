function F()
/*: new [;L;]
    [[this:Ref(L)]]
  / [L |-> (dThis:{(= v empty)}, lFProto), lFProto |-> (_:Dict, lObjectProto)]
 -> Ref(L)
  / [L |-> (_:{(= v (upd dThis "f" 1))}, lFProto), lFProto |-> same] */
{
  this.f = 1;
  return this;
}

/*: Ref(lFProto) */ (F.prototype);

F.prototype.g = "sweet";

var x = new (/*: [;lx;] lFProto */ F)();

/*: {(= v 1)} */ (x.f);
/*: {(= v "sweet")} */ (x.g);

F.prototype.g = "updated";

/*: {(= v "updated")} */ (x.g);
