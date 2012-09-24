
// storing getFirstChild on the own object itself

/*: (~lMyElt:
       {text: Str, getFirstChild: (Ref(~lMyElt)) -> Ref(~lMyElt)}
     > lROOT) */ "#weak";

var getElementsByTagName = /*:
    [;L;] (this:Ref(lMyDoc), Str) / (lMyDoc: Dict > lObjPro)
       -> Ref(L) / (lMyDoc: sameExact, L: Arr(Ref(~lMyElt)) > lArrPro) */ "#extern";

var myDoc = /*: lMyDoc */ { getElementsByTagName: getElementsByTagName };

var body = /*: [;lBodyElts;] */ (myDoc.getElementsByTagName)("body")[0];

if (body != undefined) {
  assert (/*: Ref(~lMyElt) */ body);
  body.onmousemove = "...";
  assert (/*: Ref(~lMyElt!) */ body);
}
