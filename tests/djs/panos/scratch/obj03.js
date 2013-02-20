var h = { f: function() /*: () -> Top */ {} };

var foo = function(s) 
  /*: (s:Str) / (&h: Ref(lH), lH: {Dict|(and (dom v {"f"})
                     ((sel v "f") :: () / (lObjPro: {_ : Bot} > lROOT) -> Top / sameType)
                     (= (tag (sel v "f")) "function"))} > lObjPro,
       lObjPro: {_:Bot} > lROOT)
   -> Top / sameType */ 
{

  var i /*: { Int | (>= v 0) } */ = 0;

  for (i = 0; i < 10; i += 1) {
    var func = h[s];
    if (typeof func  === 'function') {
      assert (s == "f");
  //    assert(/*: {(= (tag v) "function")}  */  (func));
  //    assert(/*: () -> Top  */  (func));
  //
  //    func();
    }
  }

};

//TODO: Try this with loop
