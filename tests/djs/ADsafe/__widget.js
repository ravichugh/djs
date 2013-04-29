/*: Global Top */ "#define";

/*: pPrim (Str v)
          (Num v)
          (Bool v)
          (= v undefined)
          (= v null) */ "#define";
 
/*: tWidget {(or  pPrim 
                  (v:: Ref(~widget))
                  (* (v:: (Global) -> tWidget) (* Of course recursive type does not work here *) *)
            )} */ "#define";

/*: (~widget: { Dict | (and 
    (implies (has v "___nodes___") (or ((sel v "___nodes___")::Ref(~htmlElts)) (= (sel v "___nodes___") undefined)))
    (implies (has v "___star___") (or (Bool (sel v "___star___")) (= (sel v "___star___") undefined)))

    (implies (has v "caller")      (bad (sel v "caller")))
    (implies (has v "callee")      (bad (sel v "callee")))
    (implies (has v "eval")        (bad (sel v "eval")))
    (implies (has v "prototype")   (bad (sel v "prototype")))
    (implies (has v "watch")       (bad (sel v "watch")))
    (implies (has v "constructor") (bad (sel v "constructor")))
    (implies (has v "__proto__")   (bad (sel v "__proto__")))
    (implies (has v "unwatch")     (bad (sel v "unwatch")))
    (implies (has v "arguments")   (bad (sel v "arguments")))
    (implies (has v "valueOf")     (bad (sel v "valueOf")))
    (implies (has v "toString")    (bad (sel v "toString")))

    (*(forall (d s) 
      (implies (and (has d s) (not (or  (= s "___nodes___")
                                        (= s "___star___")
                                        (= s "caller")
                                        (= s "callee")
                                        (= s "eval")
                                        (= s "prototype")
                                        (= s "watch")
                                        (= s "constructor")
                                        (= s "__proto__")
                                        (= s "unwatch")
                                        (= s "arguments")
                                        (= s "valueOf")
                                        (= s "toString"))))  (or ((sel d s):: Ref(~widget))
                                                                 (Str (sel d s))
                                                                 (Num (sel d s))
                                                                 (Bool (sel d s))
                                                                 (= (sel d s) undefined)
                                                                 (= (sel d s) null)
                                                             )
      )
    )*)
  )} > lObjPro) */ "#weak";

