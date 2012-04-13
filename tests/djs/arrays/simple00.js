var arr = [17, "hi", true];
arr[3] = 3; arr.push(4);
assert (arr.length == 5 && arr[5] == undefined);
