
/*: (~i: Dict > lObjPro) */ "#weak";
/*: (~p: {Dict | (Int (sel v "a"))} > lObjPro ) */ "#weak";


var a = {};


/*: a (~i, frzn) */ "#freeze";


/*: a lA */ "#thaw";

a["a"] = 10;

/*: a (~p, frzn) */ "#freeze";

