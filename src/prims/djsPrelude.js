
////////////////////////////////////////////////////////////////////////////////
//// Object.prototype

// TODO move stuff out of lang.ml/tcDref.ml. rename to __ObjectProto like
// below, and change djsDesugar.ml.


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

// TODO set this once i update setProp
// /*: [;lArray,lObject;] */ Array.constructor = Array;


"**********************************************************************";

