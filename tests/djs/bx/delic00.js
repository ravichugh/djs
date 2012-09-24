
var doQuery =
/*: [;L] (Str, Top) / ()
      -> Ref(L) / (L: {Arr(Str)|(packed v)} > lArrPro) */ "#extern";

/// extern Doc val getSelectedText :
///      d:doc{CanReadSelection d}
///   -> r:string{Selection r}

var getSelectedText =
/*: (d:Ref) / (d: {(canReadSelection v)} > lROOT)
 -> Str / same */ "#extern";

////////////////////////////////////////////////////////////////////////////////

/*: (forall (d) (canReadSelection d)) */ "#assume";

/*: callback :: (d:Ref, Top) / (d: Dict > lROOT) -> Top / same */ "#type";
var callback = function(d, e) {
  var strs = /*: [;lStrs] */ doQuery("id", e);

  // some sanity checking
  if (strs.length == 0) assert (/*: Undef */ (strs[0]));
  if (strs.length == 1) assert (/*: Str */ (strs[0]));
  if (strs.length == 1) assert (/*: Undef */ (strs[1]));
  if (strs.length == 0) assert (/*: {(not (= v "pageDetails"))} */ (strs[0]));

  if (strs.length == 1 && strs[0] === "pageDetails") {
    getSelectedText(d);
  }
};

// val callback : doc -> evt -> unit
// let callback d e = match strings (query "id" (jsonValue e)) with
//   | Cons "pageDetails" Nil -> 
//       let resp = Obj (Cons ("notes", Str (getSelectedText d)) Nil) in
//       let _ = jsonResponse e (jsonFromFine resp) in
//       ()
//   | _ -> log "some other garbage"
// 
// val start : doc -> unit
// let start doc  =
//   let _ = recvMessages (callback doc) in ()
