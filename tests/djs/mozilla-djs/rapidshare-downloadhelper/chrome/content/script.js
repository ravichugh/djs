//PV -- Definitions begin
/*: "tests/djs/mozilla-djs/rapidshare-downloadhelper/__mozilla.dref" */ "#use";
/*: "tests/djs/mozilla-djs/rapidshare-downloadhelper/__dom.dref" */ "#use";

var window /*: Ref(~lWindow) */ = null;

var Components /*: Ref(~lComponents) */ = "#extern";
var Application /*: Ref(~lApplication) */ = "#extern";

//var getBrowser /*: () -> Ref(~lBrowser) */ = "extern";


//PV -- Definitions end

//PV: changed from original form:
//var rsDownloadHelper = {};
var rsDownloadHelper = /*: Ref(~lRsDownloadHelper) */ "#extern";

//PV: rearranged this
rsDownloadHelper.initExtensionPref = function() 
  /*: () -> Top */ 
{
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

//TCs but way too slow
//var f_00 = function() /*: () -> Top */
//{
//  rsDownloadHelper.initExtensionPref();
//  rsDownloadHelper.setVer();
//  window.document.addEventListener("DOMContentLoaded", rsDownloadHelper.contentLoadedSuccess, true);
//};


//rsDownloadHelper.initialize = function() [>: () -> Top <]
//{
//  //window.addEventListener("load", f_00, false);
//};



//rsDownloadHelper.setVer = function() 
///*: () -> Top */ 
//{ 
////TODO: try-catch-finally
////		try {
//				var nsIExtensionManager	 = Components.classes["mozilla_org__extensions__manager_1"].getService(Components.interfaces.nsIExtensionManager);
//			  var rsDownloadHelperVersion     = nsIExtensionManager.getItemForID("rsDownloadHelper@yevgenyandrov.net").version;
////		} catch(ex) {
////		} finally  {
////
//        var tmp_01 = rsDownloadHelper.p;
//        assert(/*: Ref(~lRsDownloadHelperP) */ (tmp_01));
//        var Console;    //PV: moving Console definition before branch 
//        var Extension;
//			  if (tmp_01.isrsDownloadHelperNew) {
////TODO: frzn locations on function types
////				  window.setTimeout(function() /*: (this:Top) -> Top */ {
////					  var brs = getBrowser();
////				      brs.selectedTab = brs.addTab("http://www.fastyoutubedownload.com/rs/1.0/?q=n");
////				  }, 1100);
//
//				  Console = Components.classes["mozilla_org__fuel__application_1"].getService(Components.interfaces.fuelIApplication).console;
//          Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
//          Extension.prefs.setValue("isrsDownloadHelperNew", false);
//          Extension.prefs.setValue("rsDownloadHelperVersion", rsDownloadHelperVersion);
//			  }	
//        else {
//				  if (rsDownloadHelper.p.rsDownloadHelperVersion != rsDownloadHelperVersion) {
////TODO: frzn locations on function types
////					window.setTimeout(function(){
////					   var brs = getBrowser();
////					   brs.selectedTab = brs.addTab("http://www.fastyoutubedownload.com/rs/1.0/?q=u");
////					}, 1100);
//					Console = Components.classes["mozilla_org__fuel__application_1"].getService(Components.interfaces.fuelIApplication).console;
//					Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
//					Extension.prefs.setValue("rsDownloadHelperVersion", rsDownloadHelperVersion);
//				 }
//			  }
////		}
//};
//
//rsDownloadHelper.openFilePicker = function(input, defaultString) 
//  //TODO: can give more precise type here
//  /*: (this: Top, Ref(~lInput), Str) -> Top */
//{
//	var nsIFilePicker = Components.interfaces.nsIFilePicker;
//  assert(/*: Ref(~lnsIFilePicker) */ (nsIFilePicker));
////
//  var fp = Components.classes["mozilla_org__filepicker_1"].createInstance(nsIFilePicker);
//	fp.init(window, "Save As:", nsIFilePicker.modeSave);
//	
//	if (defaultString!=null) {
//		fp.defaultString = defaultString;
//		var p = defaultString.lastIndexOf(".");
//		if (p!=-1) {
//			var fileType =  defaultString.substring(p + 1);
//			fp.appendFilter(fileType, "*." + fileType);
//
//		}
//	}
//	var rv =  1; // fp.show(); //TODO: too slow
//	if (rv == nsIFilePicker.returnOK || rv == nsIFilePicker.returnReplace) {
//		  var path = fp.file.path;
//		  input.value = path;
//		  var nsIPrefBranch = Components.classes["mozilla_org__preferences_service_1"].getService(Components.interfaces.nsIPrefBranch);
//		  nsIPrefBranch.setCharPref("megaUploadDownloadHelper.folder", fp.displayDirectory.path);
//		  return fp.file;
//	};
//  return null;
//};

rsDownloadHelper.getFileName = function(doc) 
  /*: (this: Top, Ref(~lDocument)) -> Str */ 
{
//TODO: try-catch
//	try {
		var downloadlink = doc.getElementById("downloadlink");
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
	var doc = event.originalTarget;
  assert(/*: Ref(~lDocument) */ (doc));
	var loc = doc.location;			
	//var u = doc.location.toString();    //SLOW
	if (loc.href.indexOf("rapidshare.com")!=-1) {

		var downloadcounter = doc.getElementById("dl");
		if (downloadcounter) {
      var message = doc.createElement("div");
      message.style.backgroundColor = "#86f51a";
      message.style.border = "1px solid #7bd721";
      message.style.color = "#000000";
      message.innerHTML = "<B>RapidShare DownloadHelper Firefox addon message:</b><br>Now you can <u>continue browsing</u>, the file will be downloaded automatically!<br>Your automatic download will start in <font style='font-size:12px;color:#df3f4e'><b</b></font> seconds.";
			downloadcounter.parentNode.insertBefore(message, downloadcounter);
      downloadcounter.style.display='none';

			var ina /*: Int */  = window.setInterval(function()   //PV: added "window."
          /*: (this: Top) -> Top */
          {
//				var zeit = doc.getElementById("zeit");
  		  //TODO: regex support
				var num = ["a"]; //zeit.innerHTML.match(/[\d\.]+/g);
				downloadcounter.style.display='none';
				message.innerHTML = "<B>RapidShare DownloadHelper Firefox addon message:</b><br>Now you can <u>continue browsing</u>, the file will be downloaded automatically!<br>Your automatic download will start in <font style='font-size:12px;'><b>" + num[0] + "</b></font> seconds.";

				if (num[0] == "1") {
					var inaa = window.setTimeout(function() 
            //PV: added "window."
            /*: (this: Top) -> Top */ {
//						var f = doc.forms;
//						for (i=0;i<f.length;i++) {
//							if (f[i].name=="dlf") {
//								f[i].submit();
//								return;
//							}
//						}
					}, 1500);
          window.clearInterval(ina);
				}
			},1000);
		}
	}

};

//rsDownloadHelper.initialize();
