
/*: (~lMyDoc: Dict > lROOT) */ "#weak";


/// extern Doc val body : 
///      d:doc 
///   -> e:elt{ EltDoc e d && EltTagName e "body" }

var body =
/*: [;LDOC,LELT] (doc:Ref(LDOC))
  / (~lMyDoc: thwd LDOC, LDOC: d:Dict > lROOT)
 -> Ref(LELT)
  / (~lMyDoc: same, LDOC: same,
     LELT: {Dict|(and (eltDoc v d) (eltTagName v "body"))} > lEltProto) */ "#extern";


/// extern Doc val createTextNode : 
///      d:doc 
///   -> s:string 
///   -> e:elt{ EltDoc e d && EltTextValue e s }

var createTextNode =
/*: [;LDOC,LELT] (doc:Ref(LDOC), s:Str)
  / (~lMyDoc: thwd LDOC, LDOC: d:Dict > lROOT)
 -> Ref(LELT)
  / (~lMyDoc: same, LDOC: same,
     LELT: {Dict|(and (eltDoc v d) (eltTextValue v s))} > lEltProto) */ "#extern";


/// extern Elt val appendChild : 
///       cp:elt{ CanAppend cp }
///    -> cc:elt 
///    -> cd:elt{ EltParent cp cc }

// var appendChild =
// /*: (parent:Ref, child:Ref)
//   / (parent: {(canAppend v)} > lEltProto, child: d:Dict > lEltProto)
//  -> Top
//   / (parent: {(and (canAppend v) (eltParentChild v d))} > lEltProto, child: same) */ "#extern";

var appendChild =
/*: (parent:Ref, child:Ref)
  / (parent: {(canAppend v d)} > lEltProto, child: d:Dict > lEltProto)
 -> Top
  / (parent: {(and (canAppend v d) (eltParentChild v d))} > lEltProto, child: same) */ "#extern";

// var eltProto = /*: lEltProto */ {appendChild: appendChild};

////////////////////////////////////////////////////////////////////////////////

// /*: (forall (e) (implies (eltTagName e "body") (canAppend e))) */ "#assume";

/*: (forall (e1 e2) (implies (eltTagName e1 "body") (canAppend e1 e2))) */ "#assume";

/*: start :: [;L] (doc:Ref(L)) / (~lMyDoc: thwd L, L: Dict > lROOT)
          -> Top / same */ "#type";
var start = function(doc) {
  var b = /*: [;L,lFreshElt1;] */ body(doc);
  var e = /*: [;L,lFreshElt2;] */ createTextNode(doc, "Here is a new string");
  appendChild(b, e);
};


//let start doc =
//  log "Hello is running...";
//  let b = body doc in
//  let e = createTextNode doc "Here's a new string" in
//  let _ = appendChild b e in (* last child of body gets this node *)
//    ()
