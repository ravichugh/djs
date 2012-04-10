
var typeOf = function(value) {
  var s = typeof value;
  if (s == 'object') {
    if (value) { return (Array.isArray(value)) ? 'array' : 'object'; }
    else       { return 'null'; }
  }
  return s;
};

(typeOf(1));
(typeOf("hi"));
(typeOf(true));
(typeOf(null));
(typeOf({}));
(typeOf([]));
(typeOf(undefined));
