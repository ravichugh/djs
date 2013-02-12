//IMPORTANT: need to guarantee that Circle does not override area function in
//order to use the prototype's instantiation

/*: tyCircle {radius: Int, _: Bot } */ "#define";
/*: (~lCircle: tyCircle > lCircleProto) */ "#weak";

function Circle(radius) 
/*: new (this: Ref, radius: Int) / (this: Empty > lCircleProto) -> Ref(~lCircle) / () */
{
    this.radius = radius;
    /*: this (~lCircle, frzn) */ "#freeze";
    return this;
};

Circle.prototype.area = function() /*: (this: Ref(~lCircle)) -> Int */ 
{
  return 3;
};

var foo = function () /*: () -> Top */ {
  var a = new Circle(3);
  assert(/*: Ref(~lCircle) */ (a));
  a.area();
};
