var x = /*: lx */ {f:1, g:true};
var k;
var sum = 0;

/*: [&sum |-> _:Num,
     &x   |-> _:Ref(lx),
     &k   |-> _:Str,
     lx   |-> (_:Dict, lObjectProto)] -> sameType */
for (k in x) {
  if (typeof x[k] === "number") {
    sum += 1 + x[k];
  }
}

assert (typeof sum === "number");
