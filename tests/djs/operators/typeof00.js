assert (/*: {(= v "number")} */ (typeof 1));
assert (/*: {(= v "string")} */ (typeof "hi"));
assert (/*: {(= v "boolean")} */ (typeof true));
assert (/*: {(= v "object")} */ (typeof null));
assert (/*: {(= v "object")} */ (typeof {}));
assert (/*: {(= v "object")} */ (typeof []));
assert (/*: {(= v "undefined")} */ (typeof undefined));
