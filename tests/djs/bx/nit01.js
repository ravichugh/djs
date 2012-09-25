/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";
/*: "tests/djs/bx/__style01.dref" */ "#use";

/*: (forall (d) (canReadSelection d)) */ "#assume";

/*: (forall (e e2) (implies (eltTagName e "body") (canAppend e e2))) */ "#assume";
                                                  // rkc: added dummy e2 param

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

/*: searchResult :: (Ref(~doc), {World|(v::Ref(~state))}, Evt)
                 -> Ref(~state) */ "#type";
var searchResult = function (doc, w, evt) {

  var nothing_ = ["Nothing"];
  /*: nothing_ ~state */ "#freeze";
  var nothing /*: Ref(~state) */ = nothing_;

  var q = query("text", query("results", jsonOfString(textOfEvt(evt))));
  var msgs = /*: [;lMsgs] */ stringsOfJson(q);
  var world = /*: [Ref(~state)] */ getWorld(w);

  /*: world lThwd1 */ "#thaw";
  if (world[0] == "Pending") {
    var x = world[2], y = world[3];
    if (msgs.length == 0) {
      /*: world (~state, thwd lThwd1) */ "#freeze";
      return nothing;
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

      var displayedDiv = ["Displayed", div];
      /*: displayedDiv ~state */ "#freeze";
      return displayedDiv;
    }
  }
  else {
    /*: world (~state, thwd lThwd1) */ "#freeze";
    return nothing; // NitTwit.f9: should not happen
  }
};
