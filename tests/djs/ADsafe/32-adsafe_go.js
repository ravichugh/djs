/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var adsafe_id /*: Ref(~lId) */ = "#extern";
var adsafe_lib /*: Ref(~lLib) */ = "#extern";

var document  = /*: Ref(~lDocument) */ "#extern";

var error = /*: ()  -> { FLS } */ "#extern";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var make_root = 
  /*: [;L;] (root:Ref(~lNode) , id:Str) / () -> 
      Ref(L) / (L: {Arr(Top) | 
                        (and 
                           (packed v) 
                           (= (len v) 2)
                           ({(v::Ref(~lDom))} (sel v 0))
                           ({(v::Ref(lBunchProto))} (sel v 1))
                        )} > lArrPro) */ "#extern";

/*: tyInterceptor {Arr((Ref(~lId), Ref(~lDom), Ref(~lLib), Ref(~lBunch)) -> Top)|(and (packed v))} */ 
"#define";

var interceptors = /*: lIC tyInterceptor */ [];
// --------------------------------------------------------------------------


var go = function (id, f) /*: (id: Str, f: (Ref(~lDom), Ref(~lLib))-> Top ) -> Top */
{
  var dom, 
      fun /*: Top */ = null, root, i /*: {Int|(>= v 0)} */ = 0, scripts;

  //  If ADSAFE.id was called, the id better match.



  if (adsafe_id && adsafe_id !== id) {
    error();
  }

  //  Get the dom node for the widget's div container.

  root = document.getElementById(id);

  /*: root lNode */ "#thaw";

  if (root.tagName !== 'DIV') {
    error();
  }
  adsafe_id = null;

  //  Delete the scripts held in the div. They have all run, so we don't need
  //  them any more. If the div had no scripts, then something is wrong.
  //  This provides some protection against mishaps due to weakness in the
  //  document.getElementById function.

  var fn = root.getElementsByTagName;
  /*: root (~lNode, thwd lNode) */ "#freeze";
  scripts = (/*: [;lScripts;] */ fn)('script');
  i = scripts.length - 1;
  if (i < 0) {
    error();
  }
  /*: (&i:i0:{Int|(and (>= v 0) (< v (len arr)))}, 
       lScripts: arr:{Arr(Ref(~lNode))|(and (packed v))} > lArrPro)
        -> (&i: {Int|(< v 0)}, lScripts: sameType) */
   do {
    assert(/*: NotUndef */ (scripts[i]));
    root.removeChild(scripts[i]);
    i = i - 1;
  } while (i >= 0);
  root = (/*: [;lRoot;] */ make_root)(root, id);
  dom /* Ref(~lDom) */ = root[0];
  assert(/*: Ref(~lDom) */ (dom));


  // If the page has registered interceptors, call then.

  /* (&interceptors: Ref(lIC), lIC: tyInterceptor > lArrPro) -> sameType */
  for (i = 0; i < interceptors.length; i += 1) {
    fun = interceptors[i];
    if (typeof fun === 'function') {
//TODO: arrow subtyping, exceptions 
//      try {
//        assert(/*: (Ref(~lId), Ref(~lDom), Ref(~lLib), Ref(~lBunch)) -> Top */ (fun));
//        fun(id, dom, adsafe_lib, root[1]);
//      } catch (e1) {
//        ADSAFE.log(e1);
//      }
    }
  }

  //  Call the supplied function.

//  try {
    f(dom, adsafe_lib);
//  } catch (e2) {
//    ADSAFE.log(e2);
//  }
  root = null;
  adsafe_lib = null;
};
