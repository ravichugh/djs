
////////////////////////////////////////////////////////////////////////////////
//// NO LONGER USING THIS! SEE js_natives.dref
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
//// set the DJS variable [undefined] to the System !D constant [undefined]

var undefined = /*: {(= v undefined)} */ "#extern";


////////////////////////////////////////////////////////////////////////////////
//// for simplicity, modeling these constants imprecisely

var NaN = /*: Num */ "#extern";
var Infinity = /*: Num */ "#extern";
// need to add -Infinity to parser


////////////////////////////////////////////////////////////////////////////////
//// Object.prototype

var __ObjectProto_hasOwnProperty =
/*: {(and (v :: [; L1,L2] _:[this:Ref(L1), kk:Str] / [L1 |-> (dd:Dict, L2)]
             -> {Bool|(iff (= v true) (has dd {kk}))} / same)
          (v :: [A; L1,L2] _:[this:Ref(L1), kk:Str] / [L1 |-> (aa:Arr(A), L2)]
             -> {Bool|(iff (= v true) (= v "length"))} / same)
          (v :: [A; L1,L2] _:[this:Ref(L1), i:Int] / [L1 |-> (aa:Arr(A), L2)]
             -> {Bool|(implies (and (packed aa) (>= i 0))
                               (iff (= v true) (< i (len aa))))} / same))} */
"#extern";

var __ObjectProto = /*: Ref(lObjectProto) */ "#extern";
  // the Object.prototype dictionary is initialized in tcDref.ml at location
  // lObjectProto. can't define it here, since needs to set its __proto__ link
  // to the special root location lROOT.

__ObjectProto.hasOwnProperty = __ObjectProto_hasOwnProperty;

var Object = /*: lObject */ { prototype: __ObjectProto };

__ObjectProto.constructor = Object;


////////////////////////////////////////////////////////////////////////////////
///// Array.prototype

var __ArrayProto_push =
/*: [A; L1,L2]
       _:[this:Ref(L1), xx:A] / [L1 |-> (aa:Arr(A), L2)]
    -> {Int|(implies (packed aa) (= v (+ 1 (len aa))))}
     / [L1 |-> (_:{(and (v::Arr(A)) 
                   (implies (packed aa)
                            (and (packed v)
                                 (= (len v) (+ 1 (len aa)))
                                 (= (sel aa (len aa)) xx))))}, L2)] */ "#extern";

var __ArrayProto_pop =
/*: [A; L1,L2]
       _:[this:Ref(L1)] / [L1 |-> (aa:Arr(A), L2)]
    -> {(ite (packed aa)
             (and (v::A) (= v (sel aa (- (len aa) 1))))
             (or (v::A) (= v undefined)))}
     / [L1 |-> (_:{(and (v::Arr(A))
                         (implies (packed aa)
                                  (and (packed v)
                                       (= (len v) (- (len aa) 1))
                                       (> (len aa) 0))))}, L2)] */ "#extern";

var __ArrayProto = /*: lArrayProto */ {
  push: __ArrayProto_push,
  pop: __ArrayProto_pop,
};

var __isArray = /*:
  {(and (v :: [A;L1,L2]
              [[this:Ref(lArray), _:Ref(L1)]] / [L1 |-> (_:Arr(A), L2)]
           -> {(= v true)} / same)
        (v :: [;L1,L2]
              [[this:Ref(lArray), _:Ref(L1)]] / [L1 |-> (_:Dict, L2)]
           -> {(= v false)} / same)
        (v :: [[this:Ref(lArray),
                _:{(or (= (tag v) "number") (= (tag v) "boolean")
                       (= (tag v) "string") (= (tag v) "undefined")
                       (= v null))}]]
           -> {(= v false)})
)} */ "#extern";

var Array = /*: lArray */ { prototype: __ArrayProto, isArray: __isArray };

__ArrayProto.constructor = Array;


////////////////////////////////////////////////////////////////////////////////
///// Function.prototype

var __FunctionProto = /*: lFunctionProto */ { };

var Function = /*: lFunction */ { prototype: __FunctionProto };

__FunctionProto.constructor = Function;


////////////////////////////////////////////////////////////////////////////////

var end_of_djs_prelude = /*: Top */ "#extern";

