
var a = [0,1,2];

a[3] = 3;
a[4] = 4;
a[5] = 5;

assert (a.length == 6);

a.length = 2;

assert (a.length == 2);
