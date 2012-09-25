/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";
/*: "tests/djs/bx/__style01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

/*: (forall (d) (canReadSelection d)) */ "#assume";

/*: (forall (e e2) (implies (eltTagName e "body") (canAppend e e2))) */ "#assume";
                                                  // rkc: added dummy e2 param

// 
//  assume forall (s:string) (sel:string) (u:url). 
//       Selection sel 
//    && ParseUrl u s
//    && UrlHost u "search.twitter.com"
//    && UrlPath u "/search.json"
//    && UrlQuery u [("q", sel)]
//   =>  CanRequest s
// 

// type w = 
//   | Pending : evtHandler -> int -> int -> w
//   | Displayed : e:elt{CanEdit e} -> w
//   | Nothing : w

/*: (~state: {Arr(NotUndef)|(and (packed v)
                (= (sel v 0) {"Pending","Displayed","Nothing"})
                (implies (= (sel v 0) "Pending")
                         (and (= (len v) 4)
                              ((sel v 1) :: EvtHandler)
                              (Int (sel v 2))
                              (Int (sel v 3))))
                (implies (= (sel v 0) "Displayed")
                         (and (= (len v) 2)
                              ((sel v 1) :: Ref(~elt))
                              (canEdit (sel v 1))))
                (implies (= (sel v 0) "Nothing")
                         (= (len v) 1)))
             } > lArrPro) */ "#weak";

var Nothing = function () /*: () -> Ref(~state) */ {
  var data = ["Nothing"]; /*: data ~state */ "#freeze"; return data;
};

var Displayed = function (elt) /*: ({Ref(~elt)|(canEdit v)}) -> Ref(~state) */ {
  var data = ["Displayed", elt]; /*: data ~state */ "#freeze"; return data;
};

var Pending = function (h, x, y) /*: ({EvtHandler|(NotUndef v)}, Int, Int)
                                  -> Ref(~state) */ {
  var data = ["Pending", h, x, y]; /*: data ~state */ "#freeze"; return data;
};

/*: searchResult :: (Ref(~doc), {World|(v::Ref(~state))}, Evt)
                 -> Ref(~state) */ "#type";
var searchResult = function (doc, w, evt) {
  var q = query("text", query("results", jsonOfString(textOfEvt(evt))));
  var msgs = /*: [;lMsgs] */ stringsOfJson(q);
  var world = /*: [Ref(~state)] */ getWorld(w);

  /*: world lThwd1 */ "#thaw";
  if (world[0] == "Pending") {
    var x = world[2], y = world[3];
    if (msgs.length == 0) {
      /*: world (~state, thwd lThwd1) */ "#freeze";
      return Nothing();
    }
    else {
      var msg = msgs[0];
      var div = doc.createElt("div");
      var txt = doc.createTextNode(msg);
      div.appendChild(txt);
      doc.body().appendChild(div);
      var sty = div.getStyle();
      sty.setPixelLeft(x);
      sty.setPixelTop(y);
      sty.setPosition("absolute");
      sty.setBackgroundColor("white");
      sty.setBorderStyle("solid");
      sty.setBorderWidth("3px");
      sty.setBorderColor("red");
      /*: world (~state, thwd lThwd1) */ "#freeze";
      return Displayed(div);
    }
  }
  else {
    /*: world (~state, thwd lThwd1) */ "#freeze";
    return Nothing(); // NitTwit.f9: should not happen
  }
};

/*: silence :: (Ref(~doc), {World|(v::Ref(~state))}) -> Top */ "#type";
var silence = function (d, w) {
  var world = /*: [Ref(~state)] */ getWorld(w);
  /*: world lThaw1 */ "#thaw";
  if (world[0] == "Displayed") {
    d.body().removeChild(world[1]);
  }
  else if (world[0] == "Pending") {
    detach(world[1]);
  }
  /*: world (~state, thwd lThaw1) */ "#freeze";
};

// TODO remove
var hDummy = /*: {EvtHandler|(NotUndef v)} */ "#extern";

/*: selectText :: (Ref(~doc), {World|(v::Ref(~state))}, Evt)
               -> Ref(~state) */ "#type";
var selectText = function (d, w, evt) {
  var q = d.getSelectedText();
  if (q == "") {
    silence(d, w);
    return null;
  }
  else {
    var urlBase = mkUrl("http", "search.twitter.com", "/search.json");
    var u = urlAppendQuery(urlBase, "q", q);
    var s = stringOfUrl(u);
    // TODO
    // assert (UrlQuery u [("q", query)]); 
    // let h = reactPar w (request s Nil) (searchResult d) in
    silence(d, w);
    return Pending(hDummy, clientX(evt), clientY(evt));

  }
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  log("NitTwit is running...");
  // TODO
  // reactPar (makeWorld Nothing) (attachEvent (body doc) "onclick") (selectText doc);
};
