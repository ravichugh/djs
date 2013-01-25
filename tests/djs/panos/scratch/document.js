
/*: (~lNode: { a: Str } > lObjPro) */ "#weak";

/*: tyDocumentLoc { defaultView: Ref(~lNode), getElementById: () -> Top }  */ "#define";


var document /*: Ref tyDocumentLoc */ = { 
  defaultView   : null,
  getElementById: function() /*: () -> Top */ { return;}
};

var foo = function () /*: () -> Top  */
{

  var bar = function () /*: ()  -> Top  */
    {
      var view = document.defaultView;
      document.getElementById();
    }; 
};
