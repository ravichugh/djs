
//// this type handles only the fn = null case.
//// need to run with -tryAllBoxes flag.


/*: #define TtT _:Top -> Top */ "#define";

/*: #define LarrBinding Larr |-> (_:Arr(TtT), lArrayProto)*/ "#define";

/*: #define UntamperedPush
    lArrayProto |->
      (_:{(= (sel v "push") ____ArrayProto_push)}, lObjectProto) */ "#define";

/*: #define ty1 [;Larr]
    [[arr:Ref(Larr), obj:TtT, fn:{(= v null)}]] / [LarrBinding, UntamperedPush]
 -> Top / [LarrBinding, UntamperedPush] */ "#define";

var _onto = function(arr, obj, fn) /*: {(and (v::ty1))} */ {
  if (!fn) { arr.push(obj); }
  else if (fn) {
    var func = (typeof fn == "string") ? obj[fn] : fn;
    arr.push(function() /*: [[]] -> Top */ { func.call(obj); });
  }
};
