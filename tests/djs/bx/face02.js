/*: "tests/djs/bx/__dom01.dref" */ "#use";
/*: "tests/djs/bx/__files01.dref" */ "#use";

/*: (forall (s u) (implies (and
                             (parseUrl u s)
                             (urlScheme u "https")
                             (urlHost u "api.del.icio.us")
                             (urlPath u "/v1/posts/add"))
                           (canRequest s s))) */ "#assume";

    // rkc: using second dummy arg to canRequest, since in the paper
    //   canRequest is defined with two args, and used in NewsPers

/*: (forall (e) (implies (eltAttr e "className" "action actionspro_a")
                         (canReadAttr e "href"))) */ "#assume";

/*: (forall (e p) (implies (and (eltAttr p "id" "profile_name")
                                (eltParentChild p e))
                           (canReadValue e))) */ "#assume";

/*: (forall (e_label e_label_txt)
            (implies (and (eltParentChild e_label e_label_txt)
                          (eltAttr e_label "className" "label"))
                     (canReadValue e_label_txt))) */ "#assume";

/*: (forall (e_data e_label e_label_txt e_data_txt e_p)
            (implies (and
                       (eltParentChild e_p e_data)
                       (eltParentChild e_p e_label)
                       (eltParentChild e_data e_data_txt)
                       (eltParentChild e_label e_label_txt)
                       (eltAttr e_label "className" "label")
                       (eltTextValue e_label_txt "Website:"))
                     (canReadAttr e_data_txt "href"))) */ "#assume";

/*: isFriend :: (Ref(~doc)) -> Bool */ "#type";
var isFriend = function (doc) {
  var ret /*: Bool */ = false;
  var elts = /*: [{TRU};l] */ (doc.getEltsByClassName)("action actionspro_a");
  for (var i /*: {Int|(>= v 0)} */ = 0; i < elts.length; i++) {
    var u = urlOfString(elts[i].getAttr("href"));
    if (!ret && urlPath(u) == "/ajax/profile/removefriendconfirm.php") {
      ret = true;
    }
  }
  return ret;
};

/*: findName :: (Ref(~doc)) -> Str */ "#type";
var findName = function (doc) {
  return doc.getEltById("profile_name").getChild(0).getValue();
};

/*: getWebsite :: ({Ref(~elt)|(eltAttr v "className" "label")})
               -> {(or (= v null) (Str v))} */ "#type";
var getWebsite = function (elt) {
  if (elt.numChildren() == 1) {
    var txt = elt.getChild(0);
    if (txt.isTextNode() && txt.getValue() == "Website:") {
      return elt.parentNode().getChild(1).getChild(0).getAttr("href");
    }
  }
  return null;
};


/*: findWebsite :: (Ref(~doc)) -> {(or (= v null) (Str v))} */ "#type";
var findWebsite = function (doc) {
  var elts = /*: [{TRU};l] */ (doc.getEltsByClassName)("label");
  var ret /*: {(or (= v null) (Str v))} */ = null;
  for (var i /*: {Int|(>= v 0)} */ = 0; i < elts.length; i++) {
    if (ret == null && getWebsite(elts[i]) != null) {
      ret = getWebsite(elts[i]);
    }
  }
  return ret;
};

/*: callback :: (Evt) -> Top */ "#type";
var callback = function (evt) {
  log("saved!");
};

/*: saveWebsite :: (Str, Str) -> Top */ "#type";
var saveWebsite = function (friend, href) {
  var url = mkUrl("https", "api.del.icio.us", "/v1/posts/add");
  url = urlAppendQuery(url, "url", href);
  url = urlAppendQuery(url, "description", friend);
  url = urlAppendQuery(url, "replace", "yes");
  var header = "Basic" + "arjun.guha:redbull64";
  request(stringOfUrl(url), ["Authorization", header], callback);
};

/*: start :: (Ref(~doc)) -> Top */ "#type";
var start = function (doc) {
  if (doc.domain() == "facebook.com") {
    if (isFriend(doc)) {
      var friendName = findName(doc);
      var str = findWebsite(doc);
      if (str != null) {
        log("Website on " + str);
        log("Name is " + friendName);
        saveWebsite(friendName, str);
      }
      else {
        log(friendName + " does not have a website");
      }
    }
    else {
      log("Not your friend");
    }
  }
};
