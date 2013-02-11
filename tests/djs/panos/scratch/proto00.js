/*: tyCircle {Dict|(and (Int (sel v "radius")))} */ "#define";
/*: (~lCircle: tyCircle > lCircleProto) */ "#weak";

function Circle(radius) 
/*: new (this: Ref, radius: Int) / (this: Empty > lCircleProto) -> Ref(~lCircle) / () */ 
{
    this.radius = radius;
    /*: this (~lCircle, frzn) */ "#freeze";
    return this;
};

Circle.prototype.area = function() /*: () / (lCircleProto: Dict > lObjPro) -> Int / sameType */ {
   return 3;
};

var a = new Circle(3);
a.area();
