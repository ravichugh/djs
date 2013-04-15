/*: (public "dummy")     */ "#assume";

/*: PStr {Str |(public v)} */ "#define";

var foo = /*: [A] ((A) -> Str) -> PStr */ "#extern";

var source = function source_() /*: () -> Top */
{
  var f = function(x) /*: (PStr) -> Str */ { return "dummy";  };
  var t = /*: [PStr] */ foo(f);
};

