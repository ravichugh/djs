var foo = function (s) /*: (Str) -> Int */ {
  /*: (&s: Int) */
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
