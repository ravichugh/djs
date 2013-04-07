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
  /*: b lNodes */ "#thaw";
  if (b.length < 1 || !allow_focus) {
    error("default");   //PV: adding arg
  }
  b[0].focus();
  b[0].select();
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};

var selection = function (string) 
/*: (this: Ref(~lBunch), string: Str) -> Ref(~lBunch) */
{
  reject_global(this);
  string_check(string);
  var b     /*: Ref(~lNodes) */ = this.___nodes___, 
      end   /*: Int */ = 0, 
      node  /*: Ref(~lNode) */ = null,
      old   /*: Str */ = "" ,
      start /*: Int */ = 0,
      range /*: Ref(~lRange) */ = null;

  /*: b lNodes */ "#thaw";
  if (b.length === 1 && allow_focus) {
    node = b[0];
    /*: node lNode */ "#thaw";
    if (typeof node.selectionStart === 'number') {
      start = node.selectionStart;
      end = node.selectionEnd;
      old = node.value;
//TODO: this slows it down a lot
//      node.value = old.slice(0, start) + string + old.slice(end, 0);  //PV added second argument
//      node.selectionStart = node.selectionEnd = start +
//        string.length;
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
    /*: node (~lNode, thwd lNode) */ "#freeze";
  }
  /*: b (~lNodes, thwd lNodes) */ "#freeze";
  return this;
};

