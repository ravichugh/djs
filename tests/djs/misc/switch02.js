var foo = function (s) /*: (Str) -> Int */ {
  var i /*: Int */ = -1;
  switch (s) {
    case "a":
      i = 0;
      break;
    case "bb":
      i = 1;
      break;
    case "ccc":
    case "dddd":
      i = 2;
      break;
    default:
      i = -1;
      break;
  }
  return i;
};
