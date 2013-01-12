var i = 0;
var foo = function () /*: () / (&i: Str) -> Top / same */ {
  return ("hello " + i);
};
print(foo()); // fail to type check, since &i points to an int
i = "world";
print(foo()); // now it will succeed

