
////////////////////////////////////////////////////////////////////////////////
//// Object.prototype

var __ObjectProto_hasOwnProperty =
/*: {(and (v :: [; L1,L2] _:[this:Ref(L1), k:Str] / [L1 |-> (d:Dict, L2)]
                       -> {Bool|(iff (= v True) (has d {k}))} / same)
          true)} */ // TODO add case for arrays
"#extern";

var __ObjectProto = /*: Ref(lObjectProto) */ "#extern";
  // the Object.prototype dictionary is initialized in tcDref.ml at location
  // lObjectProto. can't define it here, since needs to set its __proto__ link
  // to the special root location lROOT.

/*: [;lObjectProto,lROOT] */
__ObjectProto.hasOwnProperty = __ObjectProto_hasOwnProperty;

var Object = /*: lObject */ { prototype: __ObjectProto };

/*: [;lObjectProto,lROOT;] */ __ObjectProto.constructor = Object;


////////////////////////////////////////////////////////////////////////////////
///// Array.prototype

var __ArrayProto_push =
/*: [A; L1,L2]
       _:[this:Ref(L1), x:A] / [L1 |-> (a:Arr(A), L2)]
    -> {Int|(implies (packed a) (= v (+ 1 (len a))))}
     / [L1 |-> (a':{(and (v::Arr(A)) 
                    (implies (packed a)
                             (and (packed v)
                                  (= (len v) (+ 1 (len a)))
                                  (= (sel a (len a)) x))))}, L2)] */ "#extern";

var __ArrayProto_pop =
/*: [A; L1,L2]
       _:[this:Ref(L1)] / [L1 |-> (a:Arr(A), L2)]
    -> {(ite (packed a)
             (and (v::A) (= v (sel a (- (len a) 1))))
             (or (v::A) (= v undefined)))}
     / [L1 |-> (a':{(and (v::Arr(A))
                         (implies (packed a)
                                  (and (packed v)
                                       (= (len v) (- (len a) 1))
                                       (> (len a) 0))))}, L2)] */ "#extern";

var __ArrayProto = /*: lArrayProto */ {
  push: __ArrayProto_push,
  pop: __ArrayProto_pop,
};

var Array = /*: lArray */ { prototype: __ArrayProto };

/*: [;lArrayProto,lObjectProto;] */ __ArrayProto.constructor = Array;


"**********************************************************************";

