var foo = function(s) /*: (s:Str) -> Str */ {
  var ret /*: Str */ = "";
  for (var i /*: {Int|(>= v 0)} */ = 0; i < s.length; i++) {
    ret += s.charAt(i);
  }
  return ret;
};
