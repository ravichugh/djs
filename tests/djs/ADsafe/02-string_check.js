/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
    
var error = /*: (message: Str)  / () -> Top / sameType */ "#extern";

var string_check = function (string) 
  /*: (string: Str) -> Str */
{
  if (typeof string !== 'string') {
    error("ADsafe string violation.");
  }
  return string;
};


