/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

var prefs = /*: {(= v "AppData/NewsPers/prefs.txt")} */ "#extern";

/*: (canReadFile __prefs) */ "#assume";
/*: (canReadHistory "nytimes.com") */ "#assume";
/*: (forall (s u) (implies (and (flowsFromTo __prefs s)
                                (urlHost u "digg.com"))
                           (canRequest u s))) */ "#assume";

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
