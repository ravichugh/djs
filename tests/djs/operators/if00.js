if (1) {
  "always gets here";
} else {
  assert (/*: Bot */ "never gets here");
};

if (0) {
  assert (/*: Bot */ "never gets here");
} else {
  "always gets here";
};

if (null) {
  assert (/*: Bot */ "never gets here");
} else {
  "always gets here";
};
