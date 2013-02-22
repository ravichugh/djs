/*: (~lF : Dict > lObjPro) */ "#weak";
/*: (~lA : {Dict|(implies (has v "f") ((sel v "f") :: Ref(~lF)))} > lObjPro) */ "#weak";

var f1 = function(a, s)
/*: {(and (v::(a: Ref(~lA), s: {Str|(not (= v "f"))}) -> Top)
          (v::(a: Ref(~lA), s: {Str|     (= v "f") }) -> Top)
    )}*/
{
  a[s] = null;
};

var f2 = function(a, s)
/*: (a: Ref(~lA), s: Str) -> Top */
{
  assume(s !== 'f');
  a[s] = null;
};


var f3 = function(a, s)
/*: (a: Ref(~lA), s: Str) -> Top */
{
  assume(s === 'f');
  a[s] = null;
};

var f4 = function(a, s)
/*: (a: Ref(~lA), s: Str) -> Top */
{
  a[s] = null;
};
