
/*: {(= v false)} */ (true && false);

/*: {(= v 0)} */ (0 && false);

/*: {(= v 2)} */ (1 && 2);

/*: {(= v 0)} */ (0 && 2);

/*: {(= v "")} */ ("" && 2);

/*: {(= v 2)} */ ("hi" && 2);

/*: {(= v null)} */ (null && 2);

