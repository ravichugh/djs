var abs_sum = function(x,y) 
  /*:  (x:Int, y:Int) -> 
        {(and (and (= (tag v) (tag x))
              (>= v 0))
             (>= v (+ x x)) 
             )}*/{
  if (x >= 0) {  
    if (y >= 0) {
      return x + y;    
    }
    else{
     return (x - y);      
    }    
  }
  else {
    if (y >= 0) {
      return (- x + y);
    }
    else{
     return (- x - y);
    }    
  }
};

assert (typeof (abs_sum(1,2)) == "number");

