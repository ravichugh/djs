/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

/*: (forall (e d) (implies (and (eltTagName e "a")
                                (eltDoc e d)
                                (docDomain d "newyorker.com"))
                           (canReadAttr e "href"))) */ "#assume";

/*: (forall (e d vOrig vNew u1 u2)
            (implies (and
                       (eltTagName e "a")
                       (eltDoc e d)
                       (docDomain d "newyorker.com")
                       (eltAttr e "href" vOrig)
                       (parseUrl u1 vOrig)
                       (urlHost u1 "www.newyorker.com")
                       (parseUrl u2 vNew)
                       (urlHost u2 "www.newyorker.com"))
                     (canWriteAttr e "href" vNew))) */ "#assume";

// rkc: unlike in PrintNewYorker.f9, taking a doc as a witness parameter
//   instead of existentially quantifying over it

/*: toPrintUrl :: (elem:{Ref(~elt)|(eltTagName v "a")},
                   doc: {Ref(~doc)|(and (eltDoc elem v) (docDomain v "newyorker.com"))})
               -> Top */ "#type";

var toPrintUrl = function (elem, doc) {
  var url = urlOfString(elem.getAttr("href"));
  if (urlHost(url) == "www.newyorker.com") {
    url = urlAppendQuery(url, "printable", "true");
    elem.setAttr("href", stringOfUrl(url));
  }
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  if (doc.domain() == "newyorker.com") {
    var elems = /*: [{TRU};l] */ (doc.getEltsByTagName)("a");
    for (var i /*: {Int|(>= v 0)} */ = 0; i < elems.length; i++) {
      toPrintUrl(elems[i], doc);
    }
  }
};
