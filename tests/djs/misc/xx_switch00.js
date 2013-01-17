var foo = function (s) /*: (Str) -> Int */ {
  switch (s) {
    case "a":
      return 0;
    case "bb":
      return 1;
    default:
      return "BAD";
  }
  return -1;
};
