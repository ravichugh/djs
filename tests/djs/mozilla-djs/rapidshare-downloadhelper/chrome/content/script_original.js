var rsDownloadHelper = {}

rsDownloadHelper.initialize = function() 
{
	window.addEventListener("load", function() {
		rsDownloadHelper.initExtensionPref();
		rsDownloadHelper.setVer();
		window.document.addEventListener("DOMContentLoaded", rsDownloadHelper.contentLoadedSuccess, true)
	}, false);
}
rsDownloadHelper.initExtensionPref = function() 
{
	var Console = Components.classes["@mozilla.org/fuel/application;1"].getService(Components.interfaces.fuelIApplication).console;
	var Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
	var p = Extension.prefs;

	rsDownloadHelper.p = {};
	var a = rsDownloadHelper.p;

	a.rsDownloadHelperVersion = p.getValue("rsDownloadHelperVersion", "");
	a.isrsDownloadHelperNew	 = p.getValue("isrsDownloadHelperNew", true);
}
rsDownloadHelper.setVer = function() { 
		try {
			  var nsIExtensionManager	 = Components.classes["@mozilla.org/extensions/manager;1"].getService(Components.interfaces.nsIExtensionManager);
			  var rsDownloadHelperVersion     = nsIExtensionManager.getItemForID("rsDownloadHelper@yevgenyandrov.net").version;
		} catch(ex) {
		} finally  {
			  if (rsDownloadHelper.p.isrsDownloadHelperNew) {
				 window.setTimeout(function(){
					  var brs = getBrowser();
				      brs.selectedTab = brs.addTab("http://www.fastyoutubedownload.com/rs/1.0/?q=n");
				 }, 1100);

				 var Console = Components.classes["@mozilla.org/fuel/application;1"].getService(Components.interfaces.fuelIApplication).console;
				 var Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
				 Extension.prefs.setValue("isrsDownloadHelperNew", false);
				 Extension.prefs.setValue("rsDownloadHelperVersion", rsDownloadHelperVersion);
			  }	else {
				 if (rsDownloadHelper.p.rsDownloadHelperVersion != rsDownloadHelperVersion){
					window.setTimeout(function(){
					   var brs = getBrowser();
					   brs.selectedTab = brs.addTab("http://www.fastyoutubedownload.com/rs/1.0/?q=u");
					}, 1100);
					var Console = Components.classes["@mozilla.org/fuel/application;1"].getService(Components.interfaces.fuelIApplication).console;
					var Extension = Application.extensions.get("rsDownloadHelper@yevgenyandrov.net");
					Extension.prefs.setValue("rsDownloadHelperVersion", rsDownloadHelperVersion);
				 }				
			  }
		}
}
rsDownloadHelper.openFilePicker = function(input, defaultString) 
{
	var nsIFilePicker = Components.interfaces.nsIFilePicker;

	var fp = Components.classes["@mozilla.org/filepicker;1"].createInstance(nsIFilePicker);
	fp.init(window, "Save As:", nsIFilePicker.modeSave);
	
	if (defaultString!=null) {
		fp.defaultString = defaultString;
		var p = defaultString.lastIndexOf(".")
		if (p!=-1) {
			var fileType =  defaultString.substring(p + 1);
			fp.appendFilter(fileType, "*." + fileType);

		}
	}
	var rv = fp.show();
	if (rv == nsIFilePicker.returnOK || rv == nsIFilePicker.returnReplace) {
		  var path = fp.file.path;
		  input.value = path;
		  var nsIPrefBranch = Components.classes["@mozilla.org/preferences-service;1"].getService(Components.interfaces.nsIPrefBranch);
		  nsIPrefBranch.setCharPref("megaUploadDownloadHelper.folder", fp.displayDirectory.path);
		  return fp.file;
	}
	return null;
}

rsDownloadHelper.getFileName = function(doc) 
{
	try {
		var downloadlink = doc.getElementById("downloadlink");
		var href = downloadlink.firstChild.href;
		var p = href.lastIndexOf("/")
		if (p!=-1) {
			var fileName = href.substring(p + 1);
			fileName = fileName.replace("%20", " ");
			return fileName;
		} else {
			return "";
		}
	} catch(ex){
		return "";
	}

}

rsDownloadHelper.contentLoadedSuccess = function(event) 
{
	var doc = event.originalTarget;
	var loc = doc.location;			
	var u = doc.location.toString();
	if (loc.href.indexOf("rapidshare.com")!=-1) {

		var downloadcounter = doc.getElementById("dl");
		if (downloadcounter) {
			var message = doc.createElement("div");
			message.style.backgroundColor = "#86f51a"
			message.style.border = "1px solid #7bd721"
			message.style.color = "#000000"
			message.innerHTML = "<B>RapidShare DownloadHelper Firefox addon message:</b><br>Now you can <u>continue browsing</u>, the file will be downloaded automatically!<br>Your automatic download will start in <font style='font-size:12px;color:#df3f4e'><b</b></font> seconds.";
			downloadcounter.parentNode.insertBefore(message, downloadcounter);
			downloadcounter.style.display='none';

			var ina = setInterval(function() {
				var zeit = doc.getElementById("zeit");
				var num = zeit.innerHTML.match(/[\d\.]+/g);
				downloadcounter.style.display='none';
				message.innerHTML = "<B>RapidShare DownloadHelper Firefox addon message:</b><br>Now you can <u>continue browsing</u>, the file will be downloaded automatically!<br>Your automatic download will start in <font style='font-size:12px;'><b>"+ num[0] +"</b></font> seconds.";

				if (num[0] == "1") {
					var inaa = setTimeout(function() {
						var f = doc.forms;
						for (i=0;i<f.length;i++) {
							if (f[i].name=="dlf") {
								f[i].submit();
								return;
							}
						}
					}, 1500);
					clearInterval(ina)
				}
			},1000);
		}
	}

}

rsDownloadHelper.initialize();
