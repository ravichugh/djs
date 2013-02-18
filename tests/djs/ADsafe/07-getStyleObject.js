/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
var document  = /*: Ref(~lDocument) */ "#extern";
var cache_style_node /*: Ref(~lNode) */ = "#extern";
var cache_style_object /*: Ref(~lStyle) */ = "#extern";

var defaultView = document.defaultView;

var getStyleObject = function(node) /*: (node: Ref(~lNode)) -> Ref(~lStyle) */
{

  // The getStyleObject function returns the computed style object for a node.

  if (node === cache_style_node) {
    return cache_style_object;
  }
  
  cache_style_node = node;

  cache_style_object = node.currentStyle || defaultView.getComputedStyle(node, '');

  return cache_style_object;
};

