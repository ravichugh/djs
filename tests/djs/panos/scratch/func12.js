/*: (~lRegExp: {_: Bot } > lRegExpProto)  */ "#weak";

function RegExp()
/*: (this:Ref) / (this: Empty > lRegExpProto) -> Ref(~lRegExp) / () */
{
  var self = this;
  /*: self (~lRegExp,frzn) */ "#freeze";
  return self;
};

/*: (~w: {  foo: () -> Top   } > lObjPro)  */ "#weak";

var w = /*: Ref(~w) */ "#extern";

w.foo = function ()  /*: () -> Top */ {
    return new RegExp();
};

