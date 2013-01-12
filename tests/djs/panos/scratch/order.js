var foo = function() /*: () / () -> Int / sameType */ {
  return bar();

};

var bar = function() /*: () / () -> Int / sameType */ {
  return 2;
};

print(foo());
