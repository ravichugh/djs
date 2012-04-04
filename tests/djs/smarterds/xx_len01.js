var ns = [0,1,2,3];
// BAD: there isn't a binder to describe the array value,
// so can't give the required type for frame inference...
var size = ns.length;
var i = 0;
for (; i < size; i++) ns[i] + 1;
