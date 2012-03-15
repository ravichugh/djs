
/*: #define nativeIn
    lObjectProto |-> (_:Top, lROOT),
    lFunctionProto |-> (_:Top, lObjectProto),
    &__FunctionProto |-> _:Ref(lFunctionProto)
*/ "#define";

/*: #define nativeOut
    lObjectProto |-> same,
    lFunctionProto |-> same,
    &__FunctionProto |-> same
*/ "#define";

/*: #define ty_beget
    [;L1,L2,L3;]
        [[o:Ref(L2)]] / [L2 |-> (dParent:Top, L3), nativeIn]
     -> Ref(L1) / [L1 |-> (dChild:{(= v empty)}, L2), L2 |-> same, nativeOut]
*/ '#define';

/*: #define ty_F
    ctor [;Lnew,Lpro;]
         [[this:Ref(Lnew)]] / [Lnew |-> (dThis:{(= v empty)}, Lpro)]
      -> Ref(Lnew) / same */ '#define';

var beget = function (o) /*: ty_beget */ {
  function F() /*: ty_F */ { return this; };
  F.prototype = o;
  return new /*: [;L1,L2;] L2 */ F();
};

// /*: #define ty_get_name
//     [; Lthis,Lpro; H]
//         [[this:Ref(Lthis)]]
//       / [H ++ Lthis |-> (dThis:{
//            (and ObjHas([v],"name",[H],Lpro)
//                (ObjSel([v],"name",[H],Lpro) : Str))}, Lpro)]
//      -> Str / same */ '#define';
// 
// var herb = /*: lHerb */ {
//   name : "Herb",
//   get_name : function() /*: ty_get_name */ {
//     return "Hi, I'm " ^ /*: Lthis Lpro */ this.name;
//   }
// };
// 
// var henrietta = /*: [;lHenrietta,lHerb,lObject;] */ beget(herb);
// /*: lHenrietta lHerb */ henrietta.name = "Henrietta";
// var s = (/*: [;lHenrietta,lHerb;] */ (henrietta.get_name))();
// /*: Str */ s;
// 
// /*: #define ty_get_name_2
//     [; Lthis,Lpro; ] [[this:Ref(Lthis)]] -> Int */ '#define';
// 
// /*: lHerb */ herb.get_name = function() /*: ty_get_name_2 */ { return 42; };
// var i = (/*: [;lHenrietta,lHerb;] */ (henrietta.get_name))();
// /*: Int */ i;
