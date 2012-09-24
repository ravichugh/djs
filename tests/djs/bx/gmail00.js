/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__chrome01.dref" */ "#use";

/*: (forall (e) (implies (eltTagName e "a")
                         (canReadAttr e "href"))) */ "#assume";

/*: (forall (s e) (implies (eltTagName e "a")
                           (canWriteAttr e "href" s))) */ "#assume";

/*: (forall (e) (implies (eltTagName e "a")
                         (canWriteAttr e "target" "_blank"))) */ "#assume";

/*: redirMailTo ::
       (elts:Ref) / (elts: {Arr({Ref(~elt)|(eltTagName v "a")})|(packed v)} > lArrPro)
    -> Top / same */ "#type";

var redirMailTo = function (elts) {
  for (var i /*: {Int|(>= v 0)} */ = 0; i < elts.length; i++) {
    if (matchRegexp(elts[i].getAttr("href"), "mailto:")) {
      var replaced = replaceRegexp(
                       elts[i].getAttr("href"),
                       "mailto:",
                       "https://mail.google.com/mail/?view=cm&fs=1&tf=1&to=");
      elts[i].setAttr("href", replaced);
      elts[i].setAttr("target", "_blank");
    }
  }
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  var elts = /*: [{FLS};lElts] */ (doc.getEltsByTagName)("a");
  redirMailTo(elts);
};
