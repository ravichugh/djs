var sumWeight = function(passengers, max_weight) {
  var i = 0, sum = 0, n = passengers.length;
  for (; i < n; i++) {
    var p = passengers[i];
    if (p.weight) { sum += p.weight;   }
    else          { sum += max_weight; }
  }
  return sum;
};
