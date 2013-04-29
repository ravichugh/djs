
/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var document  = /*: Ref(~lDocument) */ "#extern";
var name /*: Str */ = "#extern";
var result /*: Ref(~htmlElts) */ = "#extern";
var star    /*: Bool */         = "#extern";
var value     /*: Str */              = "#extern";       
var has_focus /*: Ref(~htmlElt) */ = "#extern";
var flipflop /*: Bool */ = "#extern"; // Used in :even/:odd processing

var getStyleObject = /*: (node: Ref(~htmlElt)) -> Ref(~lStyle) */ "#extern";

var pecker = {
    '.': function (node) /*: (Ref(~htmlElt)) -> Bool */ 
    {
      return (' ' + node.className + ' ').indexOf(' ' + name + ' ') >= 0;
    }
    ,
    '&': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */          
    {
      return node.name === name;
    },
    '_': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      return node.type === name;
    },
    '[': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      return typeof node[name] === 'string';
    },
    '[=': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */          
    {
      var member = node[name];
      return typeof member === 'string' && member === value;
    },
    '[!=': function (node)
      /*: (Ref(~htmlElt)) -> Bool */          
    {
      var member = node[name];
      return typeof member === 'string' && member !== value;
    },
    '[^=': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      var member = node[name];
      //Applying a refactoring to allow the use of slice (applied
      //later as well)
      //PV: Original code: 
      //return typeof member === 'string' &&
      //    member.slice(0, member.length) === value;
      if (typeof member === 'string') 
        return member.slice(0, member.length) === value;
      return false;
    },
    '[$=': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      var member = node[name];
      if (typeof member === 'string')
        return member.slice(-member.length, 0) === value;  //PV: added 2nd argument to slice
      return false;
    },
    '[*=': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      var member = node[name];
      if (typeof member === 'string')
        return member.indexOf(value) >= 0;
      return false;
    },
    '[~=': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      var member = node[name];
      if (typeof member === 'string')                  
        return (' ' + member + ' ').indexOf(' ' + value + ' ') >= 0;
      return false;
    },
    '[|=': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      var member = node[name];
      if (typeof member === 'string')
        return ('-' + member + '-').indexOf('-' + value + '-') >= 0;
      return false;
    }
  ,
    ':blur': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      return node !== has_focus;
    },
    ':checked': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      return node.checked;
    },
    ':disabled': function (node)
      /*: (Ref(~htmlElt)) -> Top */
    {
      return node.tagName && node.disabled;
    },
    ':enabled': function (node) 
      /*: (Ref(~htmlElt)) -> Top */
    {
      return node.tagName && !node.disabled;
    }
  ,
    ':even': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      var f;
      if (node.tagName) {
        f = flipflop;
        flipflop = !flipflop;
        return f;
      }
      return false;
    }
  ,
    ':focus': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      return node === has_focus;
    },
    ':hidden': function (node) 
      /*: (Ref(~htmlElt)) -> Top */
    {
      return node.tagName && getStyleObject(node).visibility !== 'visible';
    }
  ,
    ':odd': function (node) 
      /*: (Ref(~htmlElt)) -> Bool */
    {
      if (node.tagName) {
        flipflop = !flipflop;
        return flipflop;
      }
      return false;
    },
    ':tag': function (node) 
      /*: (Ref(~htmlElt)) -> Str */
    {
      return node.tagName;
    },
    ':text': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      return node.nodeName === '#text';
    },
    ':trim': function (node)
      /*: (Ref(~htmlElt)) -> Bool */
    {
      //TODO: regex support
      //    return node.nodeName !== '#text' || /\W/.test(node.nodeValue);  
      return false;
    },
    ':unchecked': function (node)
      /*: (Ref(~htmlElt)) -> Top */
    {
      return node.tagName && !node.checked;
    },
    ':visible': function (node)
      /*: (Ref(~htmlElt)) -> Top */
    {
      return node.tagName && getStyleObject(node).visibility === 'visible';
    }
};
