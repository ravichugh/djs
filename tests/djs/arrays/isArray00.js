// https://developer.mozilla.org/en/JavaScript/Reference/Global_Objects/isArray

assert (isArray([]));
assert (!isArray({}));
assert (!isArray(null));
assert (!isArray(undefined));
assert (!isArray(17));
assert (!isArray("Array"));
assert (!isArray(true));
assert (!isArray(false));
