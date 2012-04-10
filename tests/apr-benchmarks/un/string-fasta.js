var makeCumulative = function(table) {
  var last = null;
  var c;
  for (c in table) {
    if (last) {
      table[c] = table[c] + table[last];
      last = c;
    }
  }
};
