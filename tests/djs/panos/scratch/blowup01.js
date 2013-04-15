/*: tyQuery {Arr(Ref(lSelector))|(packed v)} */ "#define";
/*: tySel { op: Str } */ "#define";
/*: (~lSelector:  {op:Str} > lObjPro) */ "#weak";

var parse_query = function (text, id) /*: (text: Str, id: Str) -> Top */
{

  var match = /*: lA0 { Arr(Str) | (packed v) }*/ [] ,   
      query = /*: lQ  { Arr(Ref(lSelector))|(packed v)} */  [],       
      selector = /*: lS0 tySel */ { op: ''};

  /*: ( &text: Str, &query: Ref(lQ), lQ: tyQuery > lArrPro,
        &match: {(or (v::Ref(lA0)) (v::Ref(lA1)))},        
        &selector: {(or (v::Ref(lS0))) } ) -> 
        (&selector: Ref(~lSelector))
  */ 
  while(text) {
    match =  /*: lA1 {Arr(Str) | (packed v)} */ ["0", "1", "2", "3", "4", "5", "6", "7", "8"];

    if (match[1]) {

      selector = {
        op: "a"
      };
    } 
    else if (match[2]) {

      if (match[3]) {
        selector = {
          op: '[' + match[3],
          name: match[2],
          value: match[4]
        };
      }
      else {
        selector = {
          op: '[',
          name: match[2]
        };
      }
    } 

    /*: selector (~lSelector, frzn) */ "#freeze";
    
//    query.push(selector);

  };
  
};
