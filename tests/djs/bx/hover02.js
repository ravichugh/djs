/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__style01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";

/*: (forall (s) (canStyle s)) */ "#assume";

/*: (~state: [| Str, Ref(~elt) |] > lArrPro) */ "#weak";

/*: magnify :: ({World|(v::Ref(~state))}, Evt) -> Ref(~state) */ "#type";
var magnify = function (w, evt) {
  var world = /*: [Ref(~state)] */ getWorld(w);
  /*: world lThaw1 */ "#thaw";
  if (world != null) {
    var oldSize = world[0];
    var oldElt = world[1];
    oldElt.getStyle().setFontSize(oldSize);
  }
  /*: world (~state, thwd lThaw1) */ "#freeze";
  var elt = eltOfEvt(evt);
  var sty = elt.getStyle();
  sty.setFontSize("30px");
  var a = [sty.getFontSize(), elt];
  /*: a ~state */ "#freeze";
  return a;
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  var w = /*: [Ref(~state)] */ makeWorld(null);
  var handler = attachEvent(doc.body(), "onmousemove");
  // TODO
  // /*: [Ref(~state)] */ reactPar(w, handler, magnify);
};
