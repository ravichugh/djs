/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__style01.dref" */ "#use";

/*: (forall (s) (canStyle s)) */ "#assume";

/*: magnify :: (Ref(~elt)) -> Top */ "#type";
var magnify = function (elt) {
  if (!elt.isTextNode()) {
    var sty = elt.getStyle();
    var size = sty.getFontSize();
    sty.setFontSize("30px");
  }
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  var elts = (/*: [;lElts] */ (doc.body().children))();
  for (var i /*: {Int|(>= v 0)} */ = 0; i < elts.length; i++) {
    magnify(elts[i]);
  }
};
