
/*: (~lIntList: {hd: Int, tl: Ref(~lIntList)} > lObjPro) */ "#weak";

/*: (~lMyElt:
       {text: Str,
        getChild: (this:Ref(~lMyElt), Int) / (~lMyElt: frzn) -> Ref(~lMyElt) / same
       } > lROOT) */ "#weak";

var getPath = function(root,p) /*: (root:Ref(~lMyElt), Ref(~lIntList)) -> Ref(~lMyElt) */ {
  var cur  /*: Ref(~lMyElt) */   = root;
  var path /*: Ref(~lIntList) */ = p;
  while (path != undefined && cur != undefined) {
    cur = cur.getChild(path.hd);
    path = path.tl;
  }
  return cur;
};

