/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

/*: (forall (d) (canReadSelection d)) */ "#assume";

/*: callback :: (Ref(~doc), Evt) -> Top */ "#type";
var callback = function (d, e) {
  var j = query("action", jsonOfEvt(e));
  var strs = /*: [;lStrs] */ stringsOfJson(j);
  if (strs.length == 1 && strs[0] == "getSelectedUrl") {
    var resp = {url: d.getSelectedText()};
    jsonResponse(e, jsonFromDjs(resp));
  }
  else {
    log("some other garbage");
  }
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  contentScript("flbgmddimjhnbbhlkebaefaffkejcmml");
  log("I am a CONTENT SCRIPT");
  // TODO
  // let _ = recvMessages (callback doc) in ()
};
