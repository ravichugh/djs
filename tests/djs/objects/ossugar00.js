// /*: #define ty_get_name
//     [; Lthis,Lpro; H]
//         [[this:Ref(Lthis)]]
//       / [H ++ Lthis |-> (dThis:{Dict|
//            (and (objhas [v] "name" [H] Lpro)
//                ((objsel [v] "name" [H] Lpro) : Str))}, Lpro)]
//      -> Str / same */ '#define';
// 
// //// the following uses a modified objsel syntactic sugar macro
// //// in place of the above

/*: #define ty2
    [; Lthis,Lpro; H]
        (this:Ref(Lthis))
      / H + (Lthis |-> dThis:{Dict|(Str (objsel [v] "name" H Lpro))} > Lpro)
     -> Str / same */ '#define';

var herb = {
  name : "Herb",
  get_name : function() /*: ty2 */ {
    return "Hi, I'm " + this.name;
  }
};
