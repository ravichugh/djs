
var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";

function reject_global(that) {
 if (that.window) {
    error();
 }
}
