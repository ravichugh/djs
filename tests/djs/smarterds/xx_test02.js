var PI = 3.14;
var i = 0;
while (i < 10) i += i + PI;
  // BAD: i gets NonNegInt, but the addition with Num doesn't
  // preserve Int-ness, let alone NonNeg-ness
