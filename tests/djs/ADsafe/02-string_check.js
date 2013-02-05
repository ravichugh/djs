/*: "tests/djs/ADsafe/__dom.dref" */ "#use";
    
var error = /*: (message: Str)  -> { FLS } */ "#extern";

var string_check = function (string) 
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */
{
  if (typeof string !== 'string') {
    error("ADsafe string violation.");
  }
  else {
    return string;
  }
};


