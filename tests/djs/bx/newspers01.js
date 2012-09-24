/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

var prefs = /*: {(= v "AppData/NewsPers/prefs.txt")} */ "#extern";

/*: (canReadFile __prefs) */ "#assume";
/*: (canReadHistory "nytimes.com") */ "#assume";
/*: (forall (s u) (implies (and (flowsFromTo __prefs s)
                                (urlHost u "digg.com"))
                           (canRequest u s))) */ "#assume";
/*: (forall (doc elt) (implies (and (docDomain doc "nytimes.com")
                                    (flowsFromTo doc elt))
                               (canAppend doc elt))) */ "#assume";

var parseResponse =
  /*: [;L] (Str) / () -> Ref(L) / (L: {Arr(Url)|(packed v)} > lArrPro)*/
  "#extern";

/*: getPopularStories ::
      [;L] () / () -> Ref(L) / (L: {Arr(Url)|(packed v)} > lArrPro) */ "#type";
var getPopularStories = function () {
  var p = readFile(prefs);
  var url = mkUrlSimple("http", "digg.com");
  var resp = sendRequest(url, p);
  return /*: [;L] */ parseResponse(resp);
};

var munge =
  /*: [;L] (x:Ref, y:Ref) / (x: Arr(Url) > lArrPro, y: Arr(Url) > lArrPro) 
        -> Ref(L) / (x: same, y: same, L: {Arr(Url)|(packed v)} > lArrPro) */
  "#extern";

// rkc: switched 2nd arg to doc since called with root, which is a doc, not elt...
var nodesInOrder =
  /*: [;L] (x:Ref, y:Ref(~doc)) / (x: Arr(Url) > lArrPro)
        -> Ref(L) / (x: same, L: {Arr({Ref(~elt)|(flowsFromTo y v)})|(packed v)} > lArrPro) */
  "#extern";

var docAppendChild =
  /*: (d:Ref(~doc), {Ref(~elt)|(canAppend d v)}) -> Top */
  "#extern";

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (root) {
  if (root.domain() == "nytimes.com") {
    var popular = /*: [;lPopular] */ getPopularStories();
    var h = /*: [;lHistory] */ historyOnSite("nytimes.com");
    var ordering = /*: [;lOrdering,lPopular,lHistory] */ munge(popular, h);
    var inOrder = /*: [;lInOrder,lOrdering] */ nodesInOrder(ordering, root);
    for (var i /*: {Int|(>= v 0)} */ = 0; i < inOrder.length; i++) {
      // rkc: added a docAppendChild, since example calls appendChild with root...
      docAppendChild(root, inOrder[i]);
    }
  }
};

