var obj = /*: l */ {};

/*: t0 { } > lObjPro */ "#define";

/*: t1 { 
    foo: () / (l: t0) -> Top / sameType
  } > lObjPro */ "#define";

/*: t2 { 
    foo: () / (l: t0) -> Top / sameType,
    bar: () / (l: t1) -> Top / sameType
  } > lObjPro */ "#define";

obj.foo = function() /*: [;;] () -> Top */ { }; 

obj.bar = function() /*: () / (l: t2) -> Top / (l:t1) */ {
  obj.foo();
};

obj.baz = function() /*: () / (l: t2) -> Top / (l:t0) */ {
  obj.bar();
  obj.foo();
};
