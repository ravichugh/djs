// from strobe/gadgets/resistor.js
var containsNonDigit = function(inputStr) /*: (Str) -> Bool */ {
    var stringLength = inputStr.length;
    for (var i /*: { Int | (>= v 0)} */ = 0; i < stringLength; i++) {
        if ((inputStr.charAt(i) < "0") || (inputStr.charAt(i) > "9")) {
            return (true);
        }        
    }
    return (false);
};
