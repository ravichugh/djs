/*: "tests/djs/bx/__dom01.dref" */ "#use";

/*: extensionCode :: (Ref(~elt)) -> Str */ "#type";
var extensionCode = function (e) {
  var t = e.tagName();
  var a = e.getAttr('class'); // BAD: no permission to read attribute
};
