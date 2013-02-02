var owns = function(object, string) 

{
  return object && typeof object === 'object' &&
    Object.prototype.hasOwnProperty.call(object, string_check(string));
};

