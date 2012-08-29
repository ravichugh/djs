
var arr = [0,1,2];

assert (true == 0 in arr);

assert (true == 2 in arr);

assert (false == 3 in arr);

// note: can't prove anything about negative indices
(-1 in arr);

assert (true == "length" in arr);

assert (true == "push" in arr);

assert (false == "missing" in arr);
