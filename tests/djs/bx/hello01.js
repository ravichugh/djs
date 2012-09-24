/*: "tests/djs/bx/__dom01.dref" */ "#use";

// rkc: DOM.f9, Hello.f9, etc use CanAppend e with one argument,
//   but the paper uses two...

/*: (forall (e1 e2) (implies (eltTagName e1 "body") (canAppend e1 e2))) */ "#assume";

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  var b = doc.body();
  var e = doc.createTextNode("Here is a new string");
  b.appendChild(e);
};
