var a = /*: l */ {};

/*: tyd {} > lObjPro */ "#define";

/*: tyF { f: () / (l: tyd) -> Top / sameType } > lObjPro */ "#define";


a.f = function()
/*: () / (l: tyd) -> Top / sameType */
{
  a.p = 1;
};

a.g = function() 
/*: () / (l: tyF) -> Top / (l:tyd)  */
{ 
  a.f();
};
