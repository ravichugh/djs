
var a = [0,1,2];

assert (true == a.hasOwnProperty(0));

assert (true == a.hasOwnProperty(2));

assert (false == a.hasOwnProperty(3));

