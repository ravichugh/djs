/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__chrome01.dref" */ "#use";

/*: (forall (e) (implies (eltTagName e "a")
                         (canReadAttr e "href"))) */ "#assume";

/*: (forall (s e) (implies (eltTagName e "a")
                           (canWriteAttr e "href" s))) */ "#assume";

/*: (forall (e) (implies (eltTagName e "a")
                         (canWriteAttr e "target" "_blank"))) */ "#assume";

// BAD: array of elts needs to have eltTagName predicates
/*: redirMailTo_ (elts:Ref) / (elts: {Arr({Ref(~elt)|TRU})|(packed v)} > lArrPro)
              -> Top / same */ "#define";
var redirMailTo_ = function redirMailTo_(elts) /*: redirMailTo_ */ {
  for (var i /*: {Int|(>= v 0)} */ = 0; i < elts.length; i++) {
    if (matchRegexp(elts[i].getAttr("href"), "mailto:")) {

    }
  }
};
