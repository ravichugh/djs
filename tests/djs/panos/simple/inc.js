var inc = function(x) /*:  (x:Int) -> {(and (= (tag v) (tag x)) (= v (+ x 1)))}*/{
  return x + 1;
};

print(inc(1));
/*
assert (typeof (inc(2)) == "number");
assert (typeof (inc(1)) == "number");
assert (inc(1) === 2);
assert (inc(1) > 1);    //the 1 on the right is the "+ 1" in the addition
*/
//assert (inc(1) > 0);    
//assert (inc(2) > 0);    //Interesing: this cannot be proved


