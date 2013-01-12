//Function that takes three dictionaries x, y, z and adds all fields of x and 
//y into z. Prove that z contains all elements from x, y.

var merger = function (x,y)
/*: [;;H] (x:Ref, y:Ref, z:Ref) / (x: {Dict}, y: {Dict}, z: {Dict}) -> 
    Top / same
*/
{
  var z = {};
  for(c in x)  {
    z[c] = x[c];
  }
  for(c in y)  {
   z[c] = y[c];
  }
  var a = function(s) {
    return s in z;
    
  };
  return a;
  //The problem here was that I was missing the __correct__  declaration of Lz.
  //I was trying to define it in the function type, but there was no connection
  //to the type that is returned from the function. So Lz needed to be declared
  //when the return location is created. 
};


//var z = merger({a:1} , {b: 2});
//print("a: " + z("a"));
//print("b: " + z("b"));
//print("c: " + z("c"));
//print("d: " + z("d"));
