/*: "tests/djs/ADsafe/__dom.dref" */ "#use";

var reject_global = 
/*: {(and
      (v:: [;L1,L2;] (that: Ref(L1)) / (L1: d: Dict > L2) -> 
          { (implies (truthy (objsel d "window" cur L2)) FLS) } / sameExact)
      (v:: (that: Ref(~lBunch)) ->  Top)
    )} */ "#extern";

var error = /*: (message: Str)  -> { FLS } */ "#extern";

var allow_focus /*: Bool */ = "#extern";

var the_range /*: Ref(~lRange) */  = "#extern";

var string_check =
  /*: {(and (v::(string: Str) -> {(= v string)})
            (v::(string: {(not (Str v))}) -> {FLS})) } */  "#extern";

var select = function () 
/*: (this: Ref(~lBunch)) -> Top */
{
  reject_global(this);
  var b = this.___nodes___;
  /*: b htmlElts */ "#thaw";
  if (b.length < 1 || !allow_focus) {
    error("default");   //PV: adding arg
  }
  b[0].focus();
  b[0].select();
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return this;
};

var selection = function (string) 
/*: (this: Ref(~lBunch), string: Str) -> Ref(~lBunch) */
{
  reject_global(this);
  string_check(string);
  var b     /*: Ref(~htmlElts) */ = this.___nodes___, 
      end   /*: Int */ = 0, 
      node  /*: Ref(~htmlElt) */ = null,
      old   = "" ,
      start /*: Int */ = 0,
      range /*: Ref(~lRange) */ = null;

  /*: b htmlElts */ "#thaw";
  if (b.length === 1 && allow_focus) {
    node = b[0];
    /*: node htmlElt */ "#thaw";
    assume(node != null);
    if (typeof node.selectionStart === 'number') {
      start = node.selectionStart;
      end = node.selectionEnd;
      old = node.value;
      assume(typeof old === "string");
//XXX: SLOW DOWN !!! ~ 21 sec
      node.value = old.slice(0, start) /* + string  */ + old.slice(end, 0);  //PV added second argument
//XXX: SLOW DOWN !!! infinite sec !!!
      //node.selectionStart = node.selectionEnd = start + string.length;
      node.focus();
    } 
    else {
      range = node.createTextRange();
      range.expand('textedit');
      if (range.inRange(the_range)) {
        the_range.select();
        the_range.text = string;
        the_range.select();
      }
    }
    /*: node (~htmlElt, thwd htmlElt) */ "#freeze";
  }
  /*: b (~htmlElts, thwd htmlElts) */ "#freeze";
  return this;
};

