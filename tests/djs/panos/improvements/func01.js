/**
 * When foo was defined, ~w was frozen, so this is what is expected to be when
 * foo will be called. So this will FAIL.
 * In general it is possible to freeze "a" before doing the call but this gets
 * a bit cumbersome.
 */


/*: (~w: Dict > lObjPro) */ "#weak";

var foo = function() /*: () -> Top */ { };

var bar = function(a) /*: (a:Ref(~w)) -> Top */ {

  /*: a l */ "#thaw";
  foo();
  /*: a (~w, thwd l) */ "#freeze";

};
