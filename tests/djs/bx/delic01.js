/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

/*: (forall (d) (canReadSelection d)) */ "#assume";

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  var callback_doc = function (e) /*: (Evt) -> Top */ {
    var strs = /*: [;l] */ stringsOfJson(query("id", jsonOfEvt(e)));
    if (strs.length == 1) {
      var resp = ["notes", doc.getSelectedText()];
      // let _ = jsonResponse e (jsonFromFine resp) in
    }
    else {
      log("some other garbage");
    }
  };
  // TODO need to clean &doc from type of callback_doc
  recvMessages(callback_doc);
};
