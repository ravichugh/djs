/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document  = /*: Ref(~lDocument) */ "#extern";
var name /*: Str */ = "#extern";
var result /*: Ref(~lNodes) */ = "#extern";
var star    /*: Bool */         = "#extern";

var walkTheDOM = /*: ( node: Ref(~lNode), func:(Ref(~lNode)) -> Top, skip: Bool)
                   -> Top */ "#extern";

var hunter = {

  // These functions implement the hunter behaviors.

  '': function (node) /*: (node: Ref(~lNode)) / (&name: Str) -> Top / sameExact */ 
  {

    /*: node lNode */ "#thaw";
    var f = node.getElementsByTagName;        //TODO: substitute f
    var array, nodelist = (/*: [;l;] */f)(name), i, length;

    // getElementsByTagName produces a nodeList, which is one of the world's most
    // inefficient data structures. It is so slow that JavaScript's pseudo arrays
    // look terrifically swift by comparison. So we do the conversion. This is
    // easily done on some browsers, less easily on others.

    //TODO: Array + exceptions
    //try {
    //    array = Array.prototype.slice.call(nodelist, 0);
    //    result = result.length ? result.concat(array) : array;
    //} catch (ie) {
    //    length = nodelist.length;
    //    for (i = 0; i < length; i += 1) {
    //        result.push(nodelist[i]);
    //    }
    //}

    /*: node (~lNode, thwd lNode) */ "#freeze";
  }
  ,
    '+': function (node) 
      /*: (node: Ref(~lNode)) / (&name: Str) -> Top / sameType */
    {              
      node = node.nextSibling;
      name = name.toUpperCase();
      /*: (&node: Ref(~lNode)) -> (&node: sameType) */
      while (node && !node.tagName) {
        node = node.nextSibling;
      }
      if (node && node.tagName === name) {
        /*: result lResult */ "#thaw";
        result.push(node);
        /*: result (~lNodes, thwd lResult) */ "#freeze";
      }
    }
  ,
    '>': function (node) 
      /*: (node: Ref(~lNode)) / (&name: Str) -> Top / sameType */
    {
      node = node.firstChild;
      name = name.toUpperCase();
      /*: (&node: Ref(~lNode)) -> sameType  */
      while (node) {
        if (node.tagName === name) {
          /*: result lResult */ "#thaw";
          result.push(node);
          /*: result (~lNodes, thwd lResult) */ "#freeze";
        }
        node = node.nextSibling;
      }
    }
  ,
    '#': function () 
      /*: () / (&name: Str) -> Top / sameType */
    {
      var n = document.getElementById(name);
      if (n.tagName) {
        /*: result lResult */ "#thaw";
        result.push(n);
        /*: result (~lNodes, thwd lResult) */ "#freeze";
      }
    }
  ,
    '/': function (node) 
      /*: (node: Ref(~lNode)) -> Top  */
    {
      var nodes = node.childNodes;
      var i /*: {Int | (>= v 0)} */ = 0 ;

      /*:  nodes  lNList0 */ "#thaw";
      var length = nodes.length;
      var b = i < length; 
      /*: nodes (~lNList, thwd lNList0) */ "#freeze";

      /*: (&nodes: Ref(~lNList), &b : Bool, &length: Int) -> sameType */ 
      for (i = 0; b; i += 1) {
        /*: nodes lNList1 */ "#thaw";
        length = nodes.length;
        b = i < length;
        if (b) {
          /*: result lResult */ "#thaw";
          result.push(nodes[i]);
          /*: result (~lNodes, thwd lResult) */ "#freeze";
        }
        /*: nodes (~lNList, thwd lNList1) */ "#freeze";
      }
    }
  ,
    '*': function (node)
      /*: (node: Ref(~lNode)) / (&star: Bool) -> Top / sameType */
    {
      star = true;
//TODO: Sub.checkArrows      
//      walkTheDOM(
//          node, 
//          function (node1) 
//          /*: (Ref(~lNode)) -> Top */
//          {
//            /*: result lResult */ "#thaw";
//            result.push(node1);
//            /*: result (~lNodes, thwd lResult) */ "#freeze";
//          }, true);
    }
};
