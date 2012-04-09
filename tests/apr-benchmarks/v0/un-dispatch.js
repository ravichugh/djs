var dispatch = function(x,f) {
  var fn = x[f];
  return fn(x);
};
