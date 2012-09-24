/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

/*: (forall (e) (implies (eltTagName e "INPUT") (canReadValue e))) */ "#assume";
/*: (forall (e) (implies (eltTagName e "INPUT") (canWriteValue e))) */ "#assume";

/*: tyW {Ref(~elt)|(implies (not (= v null))
                            (eltTagName v "INPUT"))} */ "#define";

/*: onRequest :: (Ref(~doc), {World|(tyW v)}, Evt) -> tyW */ "#type";
var onRequest = function (d, w, evt) {
  var json = jsonOfEvt(evt);
  var strs = /*: [;lStrs] */ stringsOfJson(query("command",json));
  if (strs.length == 1 && strs[0] == "captureText") {
    log("Capturing text");
    var e = d.activeElt();
    if (e.tagName() == "INPUT") {
      jsonResponse(evt, jsonFromDjs({text: e.getValue()}));
      return e;
    }
    else {
      log("Wrong kind of text, man");
      return null;
    }
  }
  else if (strs.length == 1 && strs[0] == "pasteText") {
    log("Pasting text");
    var elt = /*: [tyW] */ getWorld(w);
    if (elt == null) {
      log("nowhere to paste");
    }
    else {
      strs = /*: [;lStrs2] */ stringsOfJson(query("text",json));
      if (strs.length == 1) {
        elt.setValue(strs[0]);
      }
      else {
        log("no .text in paste message from extension core!");
      }
    }
    return null;
  }
  else {
    log("unrecognized command from extension core!");
    return null;
  }
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  var w = /*: [tyW] */ makeWorld(null);
  // TODO
  // let _ = reactPar w recvMessages (onRequest doc) in
};
