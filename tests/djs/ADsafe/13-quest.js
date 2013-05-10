var error = /*: {( and (v::(Str) -> { FLS }) (v:: () -> { FLS }))} */ "#extern";

/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var star   /*: Bool */         = "#extern";
var name   /*: Str */ = "#extern";
var result /*: Ref(~htmlElts) */ = "#extern";
var value /*: Str */ = "#extern";
var flipflop /*: Bool */ = "#extern";
var has_focus /*: Ref(~htmlElt) */ = "#extern";

// <<<<<<<<<< 11-hunter.js <<<<<<<<<<<<<<<<<

/* heap (&result: locinvar_000050:Ref(~htmlElts) [Ref(~htmlElts)], &name:
locinvar_000052:Str [Str], ~htmlElts: frzn, ~lChecked: frzn, ~lClassNames:
frzn, ~lADsafeMarks: frzn, ~lNames: frzn, ~lPackedValues: frzn, ~lValues:
frzn, ~lOffsetHeights: frzn, ~lOffsetWidths: frzn, ~lKeys: frzn, ~lStyles:
frzn, ~lEvent: frzn, ~lEventTarget: frzn, ~lRange: frzn,
~lQuery: frzn, ~lBunches: frzn, ~lBunch: frzn, ~lStyle: frzn, ~lSelection:
frzn, ~htmlElt: frzn, ~lDocument: frzn, ~lDom: frzn, ~lF: frzn, ~lId: frzn,
~lLib: frzn) */ "#define";

/*: tyHunter { 
    "empty"   : (Ref(~htmlElt)) -> Top,
    "plus"    : (Ref(~htmlElt)) -> Top,
    "greater" : (Ref(~htmlElt)) -> Top,
    "pound"   : (Ref(~htmlElt)) -> Top,
    "slash"   : (Ref(~htmlElt)) -> Top,
    "times"   : (Ref(~htmlElt)) -> Top,
    _         : Bot } */ "#define";

/*: tySelector { Dict |
  (and 
    (has v "op") (Str (sel v "op"))
  (* Don't need this. In function quest. If the field of hunter is a function
    * this should imply that we have one of the following cases. But this won't
    * work for the population of selectors at parse_query. *)
  (*(and 
    (has v "op") ({(or  (= v "empty_") 
                        (= v "plus")
                        (= v "greater") 
                        (= v "pound") 
                        (= v "slash") 
                        (= v "star"))
                  } (sel v "op") )*)
    (implies (has v "name") (Str (sel v "name"  )))
    (implies (has v "value") (Str (sel v "value")))
  )} */ "#define";

var walkTheDOM = 
/*: ( node: Ref(~htmlElt), func:(Ref(~htmlElt)) -> Top, skip: Bool) -> Top */ "#extern";

var document  = /*: Ref(~lDocument) */ "#extern";

var arraySlice =
  /*: [A;La,Lapro,Lr] (Ref(La), Int, Int) / (La:a:Arr(A) > Lapro) 
      -> Ref(Lr) / (La: sameExact, Lr: {Arr(A)|(implies (packed a) (packed v))} > Lapro) */ "#extern";

//XXX: this is very restrictive - but will change with polymorphism over weak
//locations
var sliceHtmlElts = 
  /*: (Ref(~htmlElts), Int, Int) -> Ref(~htmlElts) */ "#extern";

var concatHtmlElts = 
  /*: (Ref(~htmlElts), Ref(~htmlElts)) -> Ref(~htmlElts) */ "#extern";


var arrayConcat =
  /*: [A;Lp,Lr] (a:Ref, b:Ref)
      / (a: Arr(A) > Lp, b:Arr(A) > Lp)
      -> Ref(Lr) / (a: sameExact, b: sameExact, Lr: {Arr(A)|(packed v)} > lArrPro) */ "#extern";



var hunter = {

  // These functions implement the hunter behaviors.

  //PV: original code
  //'': function (node) /*: (node: Ref(~htmlElt)) -> Top  */
  "empty": function (node) /*: (node: Ref(~htmlElt)) -> Top  */
  {

    var array, 
        nodelist /*: Ref(~htmlElts) */ = node.getElementsByTagName(name), 
        i /*: {Int|(>= v 0)} */ = 0, 
        length;

    // getElementsByTagName produces a nodeList, which is one of the world's most
    // inefficient data structures. It is so slow that JavaScript's pseudo arrays
    // look terrifically swift by comparison. So we do the conversion. This is
    // easily done on some browsers, less easily on others.

    //TODO: exceptions
    //try {
        //PV: original code begin
        //array = Array.prototype.slice.call(nodelist, 0);
        //PV: original code end
        
        array = sliceHtmlElts(nodelist, 0, 0);

        var tmp0 = concatHtmlElts(result, array);
        
        //PV: original code begin
        // result = result.length ? tmp0 : array;
        //PV: original code end

        var tmp_l;
        /*: result lResult */ "#thaw";
        tmp_l = result.length;
        /*: result (~htmlElts, thwd lResult) */ "#freeze";

        result = tmp_l ? tmp0 : array;

    //} catch (ie) {
        /*: nodelist lnodelist */ "#thaw";
        length = nodelist.length;
        /*: nodelist (~htmlElts, thwd lnodelist) */ "#freeze";
        
        for (i = 0; i < length; i += 1) {
          var tmp1;
          /*: nodelist lnodelist */ "#thaw";
          assume(nodelist != null);
          tmp1 = nodelist[i];
          /*: nodelist (~htmlElts, thwd lnodelist) */ "#freeze";
//          //XXX: SLOW DOWN !!! ~ 8 sec
//          /*: result lResult */ "#thaw";
//          assume(result != null);
//          assume(tmp1 != undefined);
//          result.push(tmp1);
//          /*: result (~htmlElts, thwd lResult) */ "#freeze";
        }
    //}
  },

  "plus": function (node) /*: (node: Ref(~htmlElt)) -> Top */
  { 
    node = node.nextSibling;
    name = name.toUpperCase();
    /*: (&node: Ref(~htmlElt)) -> (&node: sameType) */
    while (node && !node.tagName) {
      node = node.nextSibling;
    }
    if (node && node.tagName === name) {
      //XXX: SLOW DOWN !!! ~ 8 sec
      /*: result lResult */ "#thaw";
      result.push(node);
      /*: result (~htmlElts, thwd lResult) */ "#freeze";
    }
  },

  "greater": function (node) /*: (node: Ref(~htmlElt)) -> Top */
  {
    node = node.firstChild;
    name = name.toUpperCase();
    /*: (&node: Ref(~htmlElt)) -> sameType  */
    while (node) {
      if (node.tagName === name) {
        //XXX: SLOW DOWN !!! ~ 8 sec
        /*: result lResult */ "#thaw";
        result.push(node);
        /*: result (~htmlElts, thwd lResult) */ "#freeze";
      }
      node = node.nextSibling;
    }
  },

  //PV: Adding argument
  "pound": function (node) /*: (Ref(~htmlElt)) -> Top */
  {
    var n = document.getElementById(name);
    if (n.tagName) {
      //XXX: SLOW DOWN !!! ~ 8 sec
      /*: result lResult */ "#thaw";
      result.push(n);
      /*: result (~htmlElts, thwd lResult) */ "#freeze";
    }
  },

  "slash": function (node) /*: (node: Ref(~htmlElt)) -> Top  */
  {
    var nodes = node.childNodes;
    var i /*: {Int | (>= v 0)} */ = 0 ;

    /*:  nodes  htmlElts */ "#thaw";
    var cond = i < nodes.length; 
    /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";

    /*: (&nodes: Ref(~htmlElts), &cond : Bool) -> sameType */ 
    for (i = 0; cond; i += 1) {
      /*: nodes htmlElts */ "#thaw";
      cond = i < nodes.length;
      if (i < nodes.length) {
        var curnode = nodes[i];
        /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
        //XXX: SLOW DOWN !!! ~ 8 sec
        /*: result lResult */ "#thaw";
        result.push(curnode);
        /*: result (~htmlElts, thwd lResult) */ "#freeze";
      }
      else {
        /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
      }
    }
  },

  "times": function (node)
    /*: (node: Ref(~htmlElt)) -> Top */
  {
    star = true;
    walkTheDOM(
        node, function (_node) /*: (Ref(~htmlElt)) -> Top */ {
          //XXX: SLOW DOWN !!! ~ 8 sec
          /*: result lResult */ "#thaw";
          result.push(_node);
          /*: result (~htmlElts, thwd lResult) */ "#freeze";
        }, true);
  }
};


// >>>>>>>>>> 11-hunter.js >>>>>>>>>>>>>>>>>

//// <<<<<<<<<< 12-pecker.js <<<<<<<<<<<<<<<<<
//
//var getStyleObject = /*: (node: Ref(~htmlElt)) -> Ref(~lStyle) */ "#extern";
//
//var pecker = {
//    ".": function (node) /*: (Ref(~htmlElt)) -> Bool */ 
//    {
//      return (' ' + node.className + ' ').indexOf(' ' + name + ' ') >= 0;
//    }
//    ,
//    '&': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */          
//    {
//      return node.name === name;
//    },
//    '_': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      return node.type === name;
//    },
//    '[': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      return typeof node[name] === 'string';
//    },
//    '[=': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */          
//    {
//      var member = node[name];
//      return typeof member === 'string' && member === value;
//    },
//    '[!=': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */          
//    {
//      var member = node[name];
//      return typeof member === 'string' && member !== value;
//    },
//    '[^=': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      var member = node[name];
//      //Applying a refactoring to allow the use of slice (applied
//      //later as well)
//      //PV: Original code: 
//      //return typeof member === 'string' &&
//      //    member.slice(0, member.length) === value;
//      if (typeof member === 'string') 
//        return member.slice(0, member.length) === value;
//      return false;
//    },
//    '[$=': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      var member = node[name];
//      if (typeof member === 'string')
//        return member.slice(-member.length, 0) === value;  //PV: added 2nd argument to slice
//      return false;
//    },
//    '[*=': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      var member = node[name];
//      if (typeof member === 'string')
//        return member.indexOf(value) >= 0;
//      return false;
//    },
//    '[~=': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      var member = node[name];
//      if (typeof member === 'string')                  
//        return (' ' + member + ' ').indexOf(' ' + value + ' ') >= 0;
//      return false;
//    },
//    '[|=': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      var member = node[name];
//      if (typeof member === 'string')
//        return ('-' + member + '-').indexOf('-' + value + '-') >= 0;
//      return false;
//    }
//  ,
//    ':blur': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      return node !== has_focus;
//    },
//    ':checked': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      return node.checked;
//    },
//    ':disabled': function (node)
//      /*: (Ref(~htmlElt)) -> Top */
//    {
//      return node.tagName && node.disabled;
//    },
//    ':enabled': function (node) 
//      /*: (Ref(~htmlElt)) -> Top */
//    {
//      return node.tagName && !node.disabled;
//    },
//    ':even': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      var f;
//      if (node.tagName) {
//        f = flipflop;
//        flipflop = !flipflop;
//        return f;
//      }
//      return false;
//    },
//    ':focus': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      return node === has_focus;
//    },
//    ':hidden': function (node) 
//      /*: (Ref(~htmlElt)) -> Top */
//    {
//      return node.tagName && getStyleObject(node).visibility !== 'visible';
//    },
//    ':odd': function (node) 
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      if (node.tagName) {
//        flipflop = !flipflop;
//        return flipflop;
//      }
//      return false;
//    },
//    ':tag': function (node) 
//      /*: (Ref(~htmlElt)) -> Str */
//    {
//      return node.tagName;
//    },
//    ':text': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      return node.nodeName === '#text';
//    },
//    ':trim': function (node)
//      /*: (Ref(~htmlElt)) -> Bool */
//    {
//      //TODO: regex support
//      //    return node.nodeName !== '#text' || /\W/.test(node.nodeValue);  
//      return false;
//    },
//    ':unchecked': function (node)
//      /*: (Ref(~htmlElt)) -> Top */
//    {
//      return node.tagName && !node.checked;
//    },
//    ':visible': function (node)
//      /*: (Ref(~htmlElt)) -> Top */
//    {
//      return node.tagName && getStyleObject(node).visibility === 'visible';
//    }
//};
//// >>>>>>>>>> 12-pecker.js >>>>>>>>>>>>>>>>>
//
//
//var quest = function(query, nodes) 
///*: (query:Ref, nodes:Ref(~htmlElts)) / (query: {Arr(Ref(~lSelector))|(packed v)} > query.pro)
//    -> Ref(~htmlElts) / (query: sameExact) */
//{
//  var selector /*: Ref(~lSelector) */ = null;
//
//  var i /*: { Int | (>= v 0) } */ = 0,
//      j /*: { Int | (>= v 0) } */ = 0;
//
//  // Step through each selector.
//
//  /*: (&nodes: Ref(~htmlElts)) -> sameType */
//  for (i = 0; i < query.length; i += 1) {
//    selector = query[i];
//    var func;
//
//    /*: selector lSelector */ "#thaw";
//    assume(selector != null);
//    assume(selector.name != undefined);
//    assume(selector.op === "empty" || selector.op === "MISSING"); //to ensure the function we get has a 
//    name = selector.name;
//    assume(typeof name === "string");
//    func = hunter[selector.op];
//    /*: selector (~lSelector, thwd lSelector) */ "#freeze";   
//
//    // There are two kinds of selectors: hunters and peckers. If this is a hunter,
//    // loop through the the nodes, passing each node to the hunter function.
//    // Accumulate all the nodes it finds.
//
//    if (typeof func === 'function') {
//      if (star) {
//        error("ADsafe: Query violation: *" + selector.op +
//            (selector.name || ''));
//      }
//      result = /*: lResultEmpty {Arr(Ref(~htmlElt))|(packed v)} */ [];
//      /*: result (~htmlElts, frzn) */ "#freeze";
//
//      assert(/*: (Ref(~htmlElt)) -> Top */ (func));
//      
//      var cond00; 
//      /*: nodes htmlElts */ "#thaw";      
//      assume(nodes!= null);
//      cond00 = j < nodes.length;
//      /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//      /*: (&nodes: Ref(~htmlElts), &cond00: Bool) -> sameType */
//      for (j = 0; cond00; j += 1) {
//        var nj;
//        /*: nodes htmlElts */ "#thaw";      
//        assume(nodes!= null);
//        cond00 = j < nodes.length;
//        if (j < nodes.length) {
//          nj = nodes[j];
//          /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//          func(nj);
//        }
//        else{
//          /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//        }
//      }
//    }
//    else {
//
//      // If this is a pecker, get its function. There is a special case for
//      // the :first and :rest selectors because they are so simple.
//
//      /*: selector lSelector */ "#thaw";
//      assume(selector != null);
//      value = selector.value;
//      assume(typeof value === "string");
//
//      flipflop = false;
//      assume(selector.op === ".");
//      func = pecker[selector.op];
//      assert(/*: (Ref(~htmlElt)) -> Top */ (func));
//      /*: selector (~lSelector, thwd lSelector) */ "#freeze"; 
//      
//      if (typeof func !== 'function') {
////TODO: switch: needs some work on heap annotations
////        switch (selector.op) {
////          case ':first':
////              //result = nodes.slice(0, 1);
////              var tmpr1 = /*: [Ref(~htmlElt); Lnodes, lArrPro, lr] */ arraySlice(nodes, 0, 1);
////              /*: tmpr1 (~htmlElts, frzn) */ "#freeze";
////              result = tmpr1;
////              break;
////          case ':rest':
////              //result = nodes.slice(1, nodes.length);    //PV: added 2nd argument to slice
////              var tmpr2 = /*: [Ref(~htmlElt); Lnodes, lArrPro, lr] */ arraySlice(nodes, 0, nodes.length);
////              /*: tmpr2 (~htmlElts, frzn) */ "#freeze";
////              result = tmpr2;
////              break;
////          default:
////              error('ADsafe: Query violation: :' + selector.op);
////        }
//      }
//      else {
//
//        // For the other selectors, make an array of nodes that are filtered by
//        // the pecker function.
//
//        result = /*: lResultEmpty {Arr(Ref(~htmlElt))|(packed v)} */ [];
//        /*: result (~htmlElts, frzn) */ "#freeze";
//
//        var cond01; 
//        /*: nodes htmlElts */ "#thaw";      
//        assume(nodes!= null);
//        cond01 = j < nodes.length;
//        /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//        /*: (&nodes: Ref(~htmlElts), &cond01: Bool) -> sameType */
//        for (j = 0; cond01; j += 1) {
//          var nj;
//          /*: nodes htmlElts */ "#thaw";      
//          assume(nodes!= null);
//          cond01 = j < nodes.length;
//          if (j < nodes.length) {
//            nj = nodes[j];
//            /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//            if (func(nj)) {
//              /*: result htmlElts */ "#thaw";
//              result.push(nj);
//              /*: result (~htmlElts, thwd htmlElts) */ "#freeze";
//            }
//          }
//          else{
//            /*: nodes (~htmlElts, thwd htmlElts) */ "#freeze";
//          }
//        }
//      }
//
//    }
//    nodes = result;
//  }
//  return result;
//};
