/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__events01.dref" */ "#use";

// type w = 
//   | Pending : evtHandler -> int -> int -> w
//   | Displayed : e:elt{CanEdit e} -> w
//   | Nothing : w

/*: (~state: {Arr(NotUndef)|(and (packed v)
                (= (sel v 0) {"Pending","Displayed","Nothing"})
                (implies (= (sel v 0) "Pending")
                         (and (= (len v) 4)
                              ((sel v 1) :: EvtHandler)
                              (Int (sel v 2))
                              (Int (sel v 3))))
                (implies (= (sel v 0) "Displayed")
                         (and (= (len v) 2)
                              ((sel v 1) :: Ref(~elt))
                              (canEdit (sel v 1))))
                (implies (= (sel v 0) "Nothing")
                         (= (len v) 1)))
             } > lArrPro) */ "#weak";

// val silence : doc -> world w -> unit
// let silence d w = match getWorld w with
//   | Displayed div -> let _ = removeChild (body d) div in ()
//   | Pending eh _ _ -> detach eh; ()
//   | Nothing -> ()

/*: silence :: (Ref(~doc), {World|(v::Ref(~state))}) -> Top */ "#type";
var silence = function (d, w) {
  var world = /*: [Ref(~state)] */ getWorld(w);
  /*: world lThaw1 */ "#thaw";

  // rkc: checking this just for fun
  assert (world[0] == "Displayed"
           || world[0] == "Pending"
           || world[0] == "Nothing");

  if (world[0] == "Displayed")    { d.body().removeChild(world[1]); }
  else if (world[0] == "Pending") { detach(world[1]);               }

  /*: world (~state, thwd lThaw1) */ "#freeze";
};

