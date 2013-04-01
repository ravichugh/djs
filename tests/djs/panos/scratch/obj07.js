var a = /*: l */ {};

/*: tyd {} > lObjPro */ "#define";

/*: tyA0 {
    g: () / (l: tyd) -> Top / sameType 
  } > lObjPro */ "#define";

/*: tyA1 {
    f: () / (l: tyA0) -> Top / sameType,
    g: () / (l: tyd) -> Top / sameType 
  } > lObjPro */ "#define";

a.f = function() /*: () / (l: tyd) -> Top / sameType */ {
  a.p = 1;
};

a.g = function() /*: () / (l: tyA1) -> Top / (l:tyd)  */ { 
  a.f();
  a.g();
};
