//PV -- Definitions begin
/*: "tests/djs/mozilla-djs/rapidshare-downloadhelper/__mozilla.dref" */ "#use";
/*: "tests/djs/mozilla-djs/rapidshare-downloadhelper/__dom.dref" */ "#use";

var window /*: Ref(~lWindow) */           = "#extern";
var Components /*: Ref(~lComponents) */   = "#extern";
var Application /*: Ref(~lApplication) */ = "#extern";
var browser /*: Ref(~lBrowser) */         = "#extern";
var doc /*: Ref(~lDocument) */            = "#extern";
var elt /*: Ref(~lHTMLFormElement) */     = "#extern";
var cond /*: Bool */                      = "#extern";

var getBrowser = function() 
  /*: () / (&browser: locinvar_000273:Ref(~lBrowser)
   [Ref(~lBrowser)], &Application: locinvar_000275:Ref(~lApplication)
   [Ref(~lApplication)], &Components: locinvar_000277:Ref(~lComponents)
   [Ref(~lComponents)], &window: locinvar_000279:Ref(~lWindow) [Ref(~lWindow)],
   ~lPreferences: frzn, ~lExtensions: frzn, ~lApplication_extensions: frzn,
   ~lApplication: frzn, ~lFIApp: frzn, ~lNSIEMan: frzn, ~lNSIPBranch: frzn,
   ~lMFApplication: frzn, ~lMEManager: frzn, ~lMOFilePicker: frzn,
   ~lnsIPrefBranch: frzn, ~lMOPService: frzn, ~lnsIUpdateItem: frzn,
   ~lnsIExtensionManager: frzn, ~lComponents_classes: frzn,
   ~lComponents_interfaces: frzn, ~lComponents: frzn, ~lConsole: frzn,
   ~lRsDownloadHelper: frzn, ~lRsDownloadHelperP: frzn, ~lWindow: frzn,
   ~lnsIFilePicker: frzn, ~lFilePicker: frzn, ~lFile: frzn, ~lBrowser: frzn,
   ~lTab: frzn, ~lInput: frzn, ~lNodes: frzn, ~lChecked: frzn, ~lClassNames:
   frzn, ~lADsafeMarks: frzn, ~lNames: frzn, ~lPackedValues: frzn, ~lValues:
   frzn, ~lOffsetHeights: frzn, ~lOffsetWidths: frzn, ~lKeys: frzn, ~lStyles:
   frzn,  ~lHTMLFormElement: frzn , ~lHTMLCollection: frzn, ~lEvent: frzn,
   ~lEventTarget: frzn, ~lSelector: frzn, ~lRange: frzn, ~lQuery: frzn,
   ~lBunches: frzn, ~lBunch: frzn, ~lStyle: frzn, ~lSelection: frzn, ~lNode:
   frzn, ~lDocument: frzn, ~lDom: frzn, ~lF: frzn, ~lId: frzn, ~lLib: frzn,
   ~lURI: frzn) -> Ref(~lBrowser) / sameType */ { return browser; };

//PV -- Definitions end




//TODO: changed from original form:
//var rsDownloadHelper = {};
var rsDownloadHelper = /*: Ref(~lRsDownloadHelper) */ "#extern";

//PV: rearranged this
rsDownloadHelper.initExtensionPref = function() /*: () -> Top */ {
  //PV: changed the Component.classes url
  assert(/*: Ref(~lFIApp) */ (Components.interfaces.fuelIApplication));
	var Console = Components.classes["mozilla_org__fuel__application_1"].getService(Components.interfaces.fuelIApplication).console;
  var Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
  var p = Extension.prefs;
  var tmp_00 = {}; /*: tmp_00 (~lRsDownloadHelperP, frzn) */ "#freeze";
  rsDownloadHelper.p = tmp_00;
  var a = rsDownloadHelper.p;

  a.rsDownloadHelperVersion = p.getValue("rsDownloadHelperVersion", "");
  a.isrsDownloadHelperNew	 = p.getValue("isrsDownloadHelperNew", true);
};


rsDownloadHelper.initialize = function() /*: () -> Top */ {
  window.addEventListener(
    "load", 
    function() /*: (this:Top) -> Top */
    {
      rsDownloadHelper.initExtensionPref();
      rsDownloadHelper.setVer();
      window.document.addEventListener("DOMContentLoaded", rsDownloadHelper.contentLoadedSuccess, true);
    }, 
    false);
};



rsDownloadHelper.setVer = function() /*: () -> Top */ { 
//TODO: try-catch-finally
//		try {
        var nsIExtensionManager	 = Components.classes["mozilla_org__extensions__manager_1"].getService(Components.interfaces.nsIExtensionManager);
        var rsDownloadHelperVersion     = nsIExtensionManager.getItemForID("rsDownloadHelper@yevgenyandrov.net").version;
//		} catch(ex) {
//		} finally  {
//
        var tmp_01 = rsDownloadHelper.p;
        assert(/*: Ref(~lRsDownloadHelperP) */ (tmp_01));
        var Console;    //PV: moving Console definition before branch 
        var Extension;  //PV: same with extension
        if (tmp_01.isrsDownloadHelperNew) {
          window.setTimeout(function() /*: (this:Top) -> Top */ {
            var brs = getBrowser();
            brs.selectedTab = brs.addTab("http://www.fastyoutubedownload.com/rs/1.0/?q=n");
          }, 1100);

          Console = Components.classes["mozilla_org__fuel__application_1"].getService(Components.interfaces.fuelIApplication).console;
          Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
          Extension.prefs.setValue("isrsDownloadHelperNew", false);
          Extension.prefs.setValue("rsDownloadHelperVersion", rsDownloadHelperVersion);
        }	
        else {
          if (rsDownloadHelper.p.rsDownloadHelperVersion != rsDownloadHelperVersion) {
          window.setTimeout(function() /*: (this:Top) -> Top */ {
             var brs = getBrowser();
             brs.selectedTab = brs.addTab("http://www.fastyoutubedownload.com/rs/1.0/?q=u");
          }, 1100);
          Console = Components.classes["mozilla_org__fuel__application_1"].getService(Components.interfaces.fuelIApplication).console;
          Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
          Extension.prefs.setValue("rsDownloadHelperVersion", rsDownloadHelperVersion);
         }
        }
//		}
};

////TODO: can give more precise type here
rsDownloadHelper.openFilePicker = function(input, defaultString) 
/*: (this: Top, Ref(~lInput), Str) -> Top */ {
  var nsIFilePicker = Components.interfaces.nsIFilePicker;
  assert(/*: Ref(~lnsIFilePicker) */ (nsIFilePicker));

  var fp = Components.classes["mozilla_org__filepicker_1"].createInstance(nsIFilePicker);
  fp.init(window, "Save As:", nsIFilePicker.modeSave);
  
  if (defaultString!=null) {
    fp.defaultString = defaultString;
    var p = defaultString.lastIndexOf(".");
    if (p!=-1) {
      var fileType =  defaultString.substring(p + 1);
      fp.appendFilter(fileType, "*." + fileType);

    }
  }
  var rv =  1; // fp.show(); //TODO: slow down
  if (rv == nsIFilePicker.returnOK || rv == nsIFilePicker.returnReplace) {
      var path = fp.file.path;
      input.value = path;
      var nsIPrefBranch = Components.classes["mozilla_org__preferences_service_1"].getService(Components.interfaces.nsIPrefBranch);
      nsIPrefBranch.setCharPref("megaUploadDownloadHelper.folder", fp.displayDirectory.path);
      return fp.file;
  };
  return null;
};

rsDownloadHelper.getFileName = function(doc_) /*: (this: Top, Ref(~lDocument)) -> Str */ {
//TODO: try-catch
//	try {
    var downloadlink = doc_.getElementById("downloadlink");
    var href = downloadlink.firstChild.href;
    var p = href.lastIndexOf("/");
    if (p!=-1) {
      var fileName = href.substring(p + 1);
      fileName = fileName.replace("%20", " ");
      return fileName;
    } else {
      return "";
    }
//	} catch(ex){
    return "";
//	}
};

rsDownloadHelper.contentLoadedSuccess = function(event) 
  /*: (this: Top, Ref(~lEvent)) -> Top */
{
  //PV: defined doc at toplevel for speed up
  doc  = event.originalTarget;
  assert(/*: Ref(~lDocument) */ (doc)); //PV: this is necessary
  var loc = doc.location;			          //minor slow down
//  var u = doc.location.toString();    //major slow down: +300% - and it's not even using this value
  if (loc.href.indexOf("rapidshare.com")!=-1) {

    var downloadcounter = doc.getElementById("dl");
    if (downloadcounter) {
      var message = doc.createElement("div");
      message.style.backgroundColor = "#86f51a";
      message.style.border = "1px solid #7bd721";
      message.style.color = "#000000";
//TODO: slow down      
//      message.innerHTML = "<B>RapidShare DownloadHelper Firefox addon message:</b><br>Now you " + 
//        "can <u>continue browsing</u>, the file will be downloaded automatically!<br>Your " + 
//        "automatic download will start in <font style='font-size:12px;color:#df3f4e'><b</b></font> " + 
//        "seconds.";
//			downloadcounter.parentNode.insertBefore(message, downloadcounter);
//      downloadcounter.style.display='none';
//
      var ina /*: Int */  = window.setInterval(function()   //PV: added "window."
      /*: (this: Top) -> Top */
      {
        var zeit = doc.getElementById("zeit");
//TODO: regex support
        var num = ["a"]; //zeit.innerHTML.match(/[\d\.]+/g);
        downloadcounter.style.display='none';
        message.innerHTML = "<B>RapidShare DownloadHelper Firefox addon message:</b><br>Now " + 
          "you can <u>continue browsing</u>, the file will be downloaded automatically!<br>Your " + 
          "automatic download will start in <font style='font-size:12px;'><b>" + num[0] + 
          "</b></font> seconds.";

        if (num[0] == "1") {
          //PV: added "window."
          var inaa = window.setTimeout(function() /*: (this: Top) -> Top */ {
            //PV: Added definitions
            var f /*: Ref(~lHTMLCollection) */  = doc.forms;
            var i /*: {Int|(>= v 0)} */ = 0;
            /*: f lHTMLElts */ "#thaw";
            cond = i < f.length;
            /*: f (~lHTMLCollection, thwd lHTMLElts) */ "#freeze";

            for (i = 0; cond; i++) {
              
              /*: f lHTMLElts */ "#thaw";
              cond = i < f.length;
              if (i < f.length) {
                elt = f[i];
                /*: f (~lHTMLCollection, thwd lHTMLElts) */ "#freeze";

                /*: elt lElt */ "#thaw";
                if (elt.name=="dlf") {
                  elt.submit();
                  /*: elt (~lHTMLFormElement, thwd lElt) */ "#freeze";
                  return;
                }
                else {
                  /*: elt (~lHTMLFormElement, thwd lElt) */ "#freeze";
                }

              }
              else {
                /*: f (~lHTMLCollection, thwd lHTMLElts) */ "#freeze";
              }
            }
          }, 1500);
//TODO: issue with using ina in the expression that defines it!          
//          window.clearInterval(ina);
        }
      },1000);
    }
  }
};

//rsDownloadHelper.initialize();
