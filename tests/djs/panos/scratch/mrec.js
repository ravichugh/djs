var i = 0;

var foo = function() 
/*: () / (&i: i0: Int) -> Top / (&i: {Int | (implies (< i0 10) (= v (+ i0 1)))}) */
{
  if (i<10) {
    i = i + 1;
    //print("foo: " + i);
    bar();   
  }
};


var bar = function() {
/*: () / (&i: i0: Int) -> Top / (&i: {Int | (implies (< i0 10) (= v (+ i0 1)))}) */
  if (i<10) {
    i = i + 1;
    //print("bar: " + i);
    foo();    
  }
};

foo();
