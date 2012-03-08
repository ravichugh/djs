// https://developer.mozilla.org/en/JavaScript/Reference/Global_Objects/Array/isArray

/*: {(= v true)} */ (Array.isArray([]));
/*: {(= v false)} */ (Array.isArray({}));
/*: {(= v false)} */ (Array.isArray(null));
/*: {(= v false)} */ (Array.isArray(undefined));
/*: {(= v false)} */ (Array.isArray(17));
/*: {(= v false)} */ (Array.isArray("Array"));
/*: {(= v false)} */ (Array.isArray(true));
/*: {(= v false)} */ (Array.isArray(false));
