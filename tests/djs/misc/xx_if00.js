var foo = function(b) /*: (Bool) -> Int */ {
  if (b) { /* MISSING RETURN */ }
  else   { return 0;            }
};
