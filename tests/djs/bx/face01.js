/*: "tests/djs/bx/__dom01.dref" */ "#use";

// fragment of FacePalm from IBEX paper

/*: (forall (e) (canReadAttr e "class")) */ "#assume";
/*: (forall (p c) (implies (and (eltParentChild p c)
                                (eltTagName p "div")
                                (eltAttr p "class" "website"))
                           (canReadValue c))) */ "#assume";

/*: extensionCode :: (Ref(~elt)) -> Str */ "#type";
var extensionCode = function (e) {
  var t = e.tagName();
  var a = e.getAttr('class');
  if (t == "div" && a == "website") {
    var ch = e.getChild(0);
    return (ch == null ? "" : ch.getValue());
  }
  return "";
};
