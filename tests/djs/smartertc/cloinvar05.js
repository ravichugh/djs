var j /*: Int */ = 1;

var x = {};
var k = "f";
x[k]; // &j gets threaded through the heap frame variable during
      // this function call, so don't want to lose the cloinv Int

var f = function () /*: () -> Top */ {
  j += j;
};
