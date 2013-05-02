/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
var name   /*: Str */ = "#extern";
var getStyleObject = /*: (node: Ref(~htmlElt)) -> Ref(~lStyle) */ "#extern";

var pecker = {
    '.': function (node) /*: (Ref(~htmlElt)) -> Bool */ 
    {
      var b;
      /*: node htmlElt */ "#thaw";
      assume(node != null);
      //This line takes 7 seconds to TC ...
      b = (' ' + node.className + ' ').indexOf(' ' + name + ' ') >= 0;
      //While the following line TCs immediately!
      //b = (node.className).indexOf(name) >= 0;
      /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
      return b;
    }
};
