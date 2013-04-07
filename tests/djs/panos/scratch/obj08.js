//Weak locations allow you to have recursive types.

/*: (~lw: { 
      f: () / (~lw: frzn)-> Top /sameType, 
      g: () / (~lw: frzn)-> Top /sameType  
    } > lObjPro) */ "#weak"; 

var a  = /*: Ref(~lw) */ "#extern";

var tmp = function() /*: () -> Top */ {
  a.p = 1;
};

a.f = tmp;

a.h = function() /*: () -> Top */ { 
  a.f();
  a.g();
};
