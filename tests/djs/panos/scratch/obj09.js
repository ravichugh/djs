/*: (~la: {} > lObjPro ) */ "#weak";
/*: (~lw: { a: Ref(~la) } > lObjPro ) */ "#weak";

/*: (~ls: { f: (Ref(~la)) -> Int } > lObjPro ) */ "#weak";

var s = /*: Ref(~ls) */ "#extern";
var w = /*: Ref(~lw) */ "#extern";

assert(/*: Int */ (s.f(w.a)));

