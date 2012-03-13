if (1) {
  "always gets here";
} else {
  /*: Bot */ "never gets here";
};

if (0) {
  /*: Bot */ "never gets here";
} else {
  "always gets here";
};

if (null) {
  /*: Bot */ "never gets here";
} else {
  "always gets here";
};
