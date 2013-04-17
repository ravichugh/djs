var foo = function() /*: () -> Top */ { };

var bar = function bar_ () /*: () -> Top */ {
    foo();
    function () /*: () -> Top */ {
      bar_();
    };
};

