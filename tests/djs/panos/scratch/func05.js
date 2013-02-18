/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var make_root = function(root) /*: (root:Ref(~lNode)) -> Top */ {
  var dom_event = function (e) /*: (Ref(~lEvent)) -> Top */ {
    return;
  };  
  if (typeof root.addEventListener === 'function') {
    root.addEventListener('focus', dom_event, true);
  };
};
