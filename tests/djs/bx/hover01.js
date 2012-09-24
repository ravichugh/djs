/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__style01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";

/*: (forall (s) (canStyle s)) */ "#assume";

/*: world {Arr(Top)|(and (packed v) (= (len v) 2)
                         (Str (sel v 0))
                         ((sel v 1) :: Ref(~elt)))} */ "#define";

/*: magnify :: [;L,L2] (Ref(L?), Evt) / (L: world > lArrPro)
            -> Ref(L2) / (L: same, L2: world > lArrPro) */ "#type";
var magnify = function (worldOpt, evt) {
  if (worldOpt != null) {
    var oldSize = worldOpt[0];
    var oldElt = worldOpt[1];
    oldElt.getStyle().setFontSize(oldSize);
  }
  var elt = eltOfEvt(evt);
  var sty = elt.getStyle();
  sty.setFontSize("30px");
  return /*: L2 Arr(Top) */ [sty.getFontSize(), elt];
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  //  let w = makeWorld None in
  //  let _ = reactPar w (attachEvent (body doc) "onmousemove") magnify in
};

