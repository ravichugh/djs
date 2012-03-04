var x = {f:1};

/*: {(= v 1)} */ (x.f);
/*: {(= v undefined)} */ (x.g);

Object.prototype.g = "yipee";

/*: {(= v "yipee")} */ (x.g);
