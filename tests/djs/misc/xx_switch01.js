var foo = function (s) /*: (Str) -> Int */ {
  // since heap annotation is missing, the inferred heap
  // requires that s be unmodified (i.e. &s: {v = s})
  switch (s) {
    case "a":
      s = 0;
      break;
    case "bb":
      s = 1;
      break;
    default:
      s = -1;
      break;
  }
  return s;
};
