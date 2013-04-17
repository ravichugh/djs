var foo  = function() /*: () / () -> Top / sameType */ { };

var bar = function bar_()
/*: () / (&foo: ()  / () -> Top / sameType) -> Top / sameType */ 
{
    foo();

    function () /*: ()  -> Top */ {
      bar_();
    };
};

