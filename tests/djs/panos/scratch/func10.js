//TODO: TC this

/*: "tests/djs/mozilla-djs/rapidshare-downloadhelper/__mozilla.dref" */ "#use";
/*: "tests/djs/mozilla-djs/rapidshare-downloadhelper/__dom.dref" */ "#use";

var window /*: Ref(~lWindow) */ = "#extern";

var foo = function(doc) /*: (Ref(~lDocument)) -> Top */ {

  var ina  = window.setInterval(
      function() /*: (this: Top) -> Top */ {
        var zeit = doc.getElementById("zeit");
        window.clearInterval(ina);
      },
      1000);
};
