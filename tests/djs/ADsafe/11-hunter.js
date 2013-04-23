/*: heap (&result: locinvar_000050:Ref(~lNodes) [Ref(~lNodes)], &name:
locinvar_000052:Str [Str], ~lNodes: frzn, ~lChecked: frzn, ~lClassNames:
frzn, ~lADsafeMarks: frzn, ~lNames: frzn, ~lPackedValues: frzn, ~lValues:
frzn, ~lOffsetHeights: frzn, ~lOffsetWidths: frzn, ~lKeys: frzn, ~lStyles:
frzn, ~lEvent: frzn, ~lEventTarget: frzn, ~lSelector: frzn, ~lRange: frzn,
~lQuery: frzn, ~lBunches: frzn, ~lBunch: frzn, ~lStyle: frzn, ~lSelection:
frzn, ~lNode: frzn, ~lDocument: frzn, ~lDom: frzn, ~lF: frzn, ~lId: frzn,
~lLib: frzn) */ "#define";



var walkTheDOM = 
/*: ( node: Ref(~lNode), func:(Ref(~lNode)) / heap -> Top / sameType, 
      skip: Bool) -> Top */ "#extern";
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document  = /*: Ref(~lDocument) */ "#extern";
var name      /*: Str */ = "#extern";
var result    /*: Ref(~lNodes) */ = "#extern";
var star      /*: Bool */         = "#extern";

var arraySlice =
  /*: [A;La,Lapro,Lr] (Ref(La), Int, Int) / (La:a:Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: {Arr(A)|(implies (packed a) (packed v))} > Lapro) */ "#extern";

var arrayConcat =
  /*: [A;Lp,Lr] (a:Ref, b:Ref)
      / (a: Arr(A) > Lp, b:Arr(A) > Lp)
      -> Ref(Lr) / (a: sameExact, b: sameExact, Lr: {Arr(A)|(packed v)} > lArrPro) */ "#extern";

var hunter = {

  // These functions implement the hunter behaviors.

  '': function (node) /*: (node: Ref(~lNode)) -> Top  */
  {

    /*: node lNode */ "#thaw";
    var f = node.getElementsByTagName;
    var array, nodelist = (/*: [;l;] */f)(name), i /*: {Int|(>= v 0)} */ = 0, length;

    // getElementsByTagName produces a nodeList, which is one of the world's most
    // inefficient data structures. It is so slow that JavaScript's pseudo arrays
    // look terrifically swift by comparison. So we do the conversion. This is
    // easily done on some browsers, less easily on others.

    //TODO: exceptions
    //try {
        //PV: original code begin
        //array = Array.prototype.slice.call(nodelist, 0);
        //PV: original code end
        
        array = /*: [Ref(~lNode); l,lArrPro, larray] */ arraySlice(nodelist, 0, 0);

        /*: result lResult */ "#thaw";
        assume(result != null);
        var tmp0 = /*: [Ref(~lNode);lArrPro,lr2,lResult,larray] */ arrayConcat(result,array);
        
        //PV: original code begin
        // result = result.length ? tmp0 : array;
        //PV: original code end

        if (result.length) {
          /*: result (~lNodes, thwd lResult) */ "#freeze";
          /*: tmp0  (~lNodes, frzn) */ "#freeze";
          result = tmp0;
        } else {
          /*: result (~lNodes, thwd lResult) */ "#freeze";
          /*: array (~lNodes, frzn) */ "#freeze";
          result = array;
        }

    //} catch (ie) {
        length = nodelist.length;
        for (i = 0; i < length; i += 1) {
          /*: result lResult */ "#thaw";
          result.push(nodelist[i]);
          /*: result (~lNodes, thwd lResult) */ "#freeze";
        }
    //}

    /*: node (~lNode, thwd lNode) */ "#freeze";
  },
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
  },
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
    },
    '#': function () 
      /*: () / (&name: Str) -> Top / sameType */
    {
      var n = document.getElementById(name);
      if (n.tagName) {
        /*: result lResult */ "#thaw";
        result.push(n);
        /*: result (~lNodes, thwd lResult) */ "#freeze";
      }
    },
    '/': function (node) 
      /*: (node: Ref(~lNode)) -> Top  */
    {
      var nodes = node.childNodes;
      var i /*: {Int | (>= v 0)} */ = 0 ;

      /*:  nodes  lNodes */ "#thaw";
      var cond = i < nodes.length; 
      /*: nodes (~lNodes, thwd lNodes) */ "#freeze";

      /*: (&nodes: Ref(~lNodes), &cond : Bool) -> sameType */ 
      for (i = 0; cond; i += 1) {
        /*: nodes lNodes */ "#thaw";
        cond = i < nodes.length;
        if (i < nodes.length) {
          var curnode = nodes[i];
          /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
          /*: result lResult */ "#thaw";
          result.push(curnode);
          /*: result (~lNodes, thwd lResult) */ "#freeze";
        }
        else {
          /*: nodes (~lNodes, thwd lNodes) */ "#freeze";
        }
      }
    },
    '*': function (node)
      /*: (node: Ref(~lNode)) / (&star: Bool) -> Top / sameType */
    {
      star = true;
      walkTheDOM(
          node, function (_node) /*: (Ref(~lNode)) -> Top */ {
            /*: result lResult */ "#thaw";
            result.push(_node);
            /*: result (~lNodes, thwd lResult) */ "#freeze";
          }, true);
    }
};
