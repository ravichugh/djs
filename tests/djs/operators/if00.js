if (1) {
  "always gets here";
} else {
  assert (/*: {FLS} */ "never gets here");
};

if (0) {
  assert (/*: {FLS} */ "never gets here");
} else {
  "always gets here";
};

if (null) {
  assert (/*: {FLS} */ "never gets here");
} else {
  "always gets here";
};
