/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";

/*: (forall (d) (canReadSelection d)) */ "#assume";

/*: onMouseUp :: (Ref(~doc), {World|TRU}, Evt) -> Top */ "#type";
var onMouseUp = function (d, w, evt) {
  jsonRequest(jsonFromDjs({'greeting': d.getSelectedText()}));
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (d) {
  var w = /*: [Top] */ makeWorld(null);
  var handler = attachEvent(d.body(), "onmouseup");
  // TODO
  // let _ = reactPar w (attachEvent (body d) "onmouseup") (onMouseUp d) in
};
