var Flashblock = {

    // File mode flags

    MODE_RDONLY   : 0x01,
    MODE_WRONLY   : 0x02,
    MODE_RDWR     : 0x04,
    MODE_CREATE   : 0x08,
    MODE_APPEND   : 0x10,
    MODE_TRUNCATE : 0x20,
    MODE_SYNC     : 0x40,
    MODE_EXCL     : 0x80,

    /// USER STYLESHEET FUNCTIONS

    // Returns a nsIFile for the specified file in the profile chrome directory
    getUserChromeFile : function(fileName) {
        var NSIFILE = Components.interfaces.nsIFile;
        var dirLocator = Components.classes["@mozilla.org/file/directory_service;1"]
                                   .getService(Components.interfaces.nsIProperties);
        var userChromePath = dirLocator.get("UChrm", NSIFILE).path;

        var file = Components.classes["@mozilla.org/file/local;1"]
                             .createInstance(Components.interfaces.nsILocalFile);

        file.initWithPath(userChromePath);
        file.append(fileName);

        return file;
    },

    // Returns the contents of the specified file in the profile chrome directory
    readUserChromeFile : function (fileName) {
        var fileContents = "";
        var file = Flashblock.getUserChromeFile(fileName);

        if(file.exists()) {
            var ioFlags = this.MODE_RDONLY;

            // Get an input stream
            var is = Components.classes["@mozilla.org/network/file-input-stream;1"]
                               .createInstance( Components.interfaces.nsIFileInputStream);
            is.init(file, ioFlags, 0, is.CLOSE_ON_EOF);
            var sis = Components.classes["@mozilla.org/scriptableinputstream;1"]
                                .createInstance( Components.interfaces.nsIScriptableInputStream);
            sis.init(is);

            // Read the file in
            while(sis.available() > 0)
                fileContents += sis.read(sis.available());

            // Close streams
            is.close();
            sis.close();
        }

        return fileContents;
    },

    // Writes the specified contents into the specified file in the profile chrome directory
    writeUserChromeFile : function (fileName, fileContents) {
        var file = Flashblock.getUserChromeFile(fileName);
        var ioFlags = this.MODE_WRONLY | this.MODE_CREATE | this.MODE_TRUNCATE;
        var perm = 0644;

        var os = Components.classes["@mozilla.org/network/file-output-stream;1"]
                           .createInstance( Components.interfaces.nsIFileOutputStream);
        os.init(file, ioFlags, perm, 0);

        var result = os.write(fileContents, fileContents.length);
        os.close();

        return result;
    },

    // Checks the if the user stylesheet already contains the import statement
    userStyleSheetHasImport : function () {
        var fileContents = Flashblock.readUserChromeFile('userContent.css');
        var re = new RegExp("^[ \t]*@import.*chrome://flashblock/content/flashblock.css", "m");

        return re.test(fileContents);
    },

    // Adds a CSS import statement for the flashblock stylesheet
    addImportToUserStylesheet : function (fileName) {
        var importStr = "@import url(chrome://flashblock/content/flashblock.css);"

        var fileContents = Flashblock.readUserChromeFile('userContent.css');
        var re = new RegExp("^[ \t]*@import.*chrome://flashblock/content/flashblock.css", "m");

        if(re.test(fileContents))
            return true;

        fileContents = importStr + "\n" + fileContents;

        var ret = Flashblock.writeUserChromeFile(fileName, fileContents);
        return (ret == fileContents.length);
    },

    // Removes the CSS import statement for the flashblock stylesheet
    removeImportFromUserStylesheet : function (fileName) {
        var fileContents = Flashblock.readUserChromeFile(fileName);
        var re = new RegExp("^[ \t]*@import.*chrome://flashblock/content/flashblock.css.*(\n)?$", "mg");

        if(re.test(fileContents)) {
            fileContents = fileContents.replace(re, '');
            var ret = Flashblock.writeUserChromeFile(fileName, fileContents);
            return (ret == fileContents.length)
        } else {
            return true;
        }
    },

    _whitelistTargetEnabled: true,

/// PREF FUNCTIONS
	// was flashblockPrefObserver
	prefObserver : {
		observe: function(subject, topic, data) {
			if(data == "flashblock.whitelist")
				Flashblock.loadWhitelist();
			else if(data == "flashblock.enabled") {
				gFlashblockEnabled = Flashblock.isEnabled();
				Flashblock.setButtonState(gFlashblockEnabled);
			}
			else if(data == "javascript.enabled") {
				Flashblock.setButtonState(gFlashblockEnabled);
			}
			else if(data == "flashblock.silverlight.blocked") {
				gSilverblockEnabled = Flashblock.isSilverlightEnabled();
			}
			else if(data == "flashblock.whitelist.includeTarget") {
				Flashblock._whitelistTargetEnabled = Flashblock.isTargetEnabled();
			}
		},

		QueryInterface : function (aIID) {
			if (aIID.equals(Components.interfaces.nsIObserver) || 
				aIID.equals(Components.interfaces.nsISupports) ||
				aIID.equals(Components.interfaces.nsISupportsWeakReference))
				return this;
			throw Components.results.NS_NOINTERFACE;
		}
	},

	// was addFlashblockPrefObserver
	addPrefObserver : function () {
		var prefs = Components.classes["@mozilla.org/preferences-service;1"]
					.getService(Components.interfaces.nsIPrefBranch);

		var pbi = prefs.QueryInterface(Components.interfaces.nsIPrefBranchInternal);
		pbi.addObserver("flashblock.", Flashblock.prefObserver, true);
		pbi.addObserver("javascript.enabled", Flashblock.prefObserver, true);
	},


/// WHITELIST FUNCTIONS

	// Loads the whitelist into the global array
	loadWhitelist : function () {
		var flashblockPref = FBlockUtils.getWhitelist();
		gFlashblockWhitelist = new Array();
		if (flashblockPref)
		    gFlashblockWhitelist = flashblockPref.split(",");
	},

	checkHostInWhitelist : function (host) {
		if (!host)
			return false;
		for (var i = 0; i < gFlashblockWhitelist.length; i++) {
			// Handle *
			var expr = gFlashblockWhitelist[i];
			expr = expr.replace(/\./g, "\\.");
			expr = expr.replace(/\-/g, "\\-");
			expr = expr.replace(/\?/g, "\\?");
			expr = expr.replace(/\+/g, "\\+");
			//expr = expr.replace(/\*/g, "[A-Za-z0-9_\\-\\.]*")
			//expr = expr.replace(/\*/g, "[^ \t\v\n\r\f]*")
			expr = expr.replace(/\*/g, ".*")
			if (expr.slice(-2) != ".*")
				expr = expr + ".*"
			expr = expr + "$"; // "^" + 

			var re = new RegExp(expr);
			if(re.test(host))
				return true;
		}
		return false;
	},

	checkWhitelist : function (url) {
		if(!FBlockUtils.isLocalBlocked()) {
			if(url.protocol == "file:")
				return true;
		}

		return this.checkHostInWhitelist(url.host) ||  this.checkHostInWhitelist(url.spec);
	},

	getTargetURI : function(node) {
		var targetURI;
		try {
			// Get object URI in the same way as nsObjectLoadingContent::LoadObject()
			var relativeURI;
			switch (node.localName.toLowerCase()) {
				case "object":
					relativeURI = node.getAttribute("data") || node.getAttribute("src") || "";
					if (!relativeURI) {
						var params = node.getElementsByTagName("param");

						for (var ii = 0; ii < params.length; ii++) {
							var name = params[ii].getAttribute("name");
							switch (name) {
								case "movie":
								case "src":
									relativeURI = params[ii].getAttribute("value");
									break;
							}
						}
					}
					break;
				case "embed":
					relativeURI = node.getAttribute("src") || "";
					break;
			}

			var ios = Components.classes["@mozilla.org/network/io-service;1"]
				.getService(Components.interfaces.nsIIOService);
			var baseURI = ios.newURI(node.baseURI, null, null);
			var codeBase = node.getAttribute("codebase");
			if (codeBase) {
				try {
					baseURI = ios.newURI(codeBase, node.ownerDocument.characterSet, baseURI);
				} catch (e) {}  // Ignore invalid codebase attribute
			}
			targetURI = ios.newURI(relativeURI, node.ownerDocument.characterSet, baseURI);
		}
		catch (e) {
			Components.utils.reportError(e);
		}
		return targetURI;
	},

	blockedByContentPolicy : function(node) {
		try {
			var uri = this.getTargetURI(node);
			// Ask content policy whether this object is already blocked
			var ios = Components.classes["@mozilla.org/network/io-service;1"]
				.getService(Components.interfaces.nsIIOService);
			var requestOrigin = ios.newURI(node.ownerDocument.location, null, null);
			var contentPolicy = Components.classes["@mozilla.org/layout/content-policy;1"]
				.getService(Components.interfaces.nsIContentPolicy);
			var blockType = contentPolicy.shouldLoad(Components.interfaces.nsIContentPolicy.TYPE_OBJECT,
						uri, requestOrigin, node,
						node.getAttribute("type"), null);
			return blockType != Components.interfaces.nsIContentPolicy.ACCEPT;
		}
		catch (e) {
			Components.utils.reportError(e);
			return false;
		}
	},

	checkLoadFlash : function (e) {
		if(!gFlashblockEnabled ||
			(e.target &&
				(Flashblock.checkWhitelist(e.target.ownerDocument.location) ||
				(Flashblock._whitelistTargetEnabled && Flashblock.checkWhitelist(Flashblock.getTargetURI(e.target))) ||
				Flashblock.blockedByContentPolicy(e.target)))
			) {
			e.preventDefault();
		}
		e.stopPropagation();
	},

	checkLoadSilver : function (e) {
		if(!gFlashblockEnabled ||
			!gSilverblockEnabled ||
			(e.target &&
				(Flashblock.checkWhitelist(e.target.ownerDocument.location) ||
				(Flashblock._whitelistTargetEnabled && Flashblock.checkWhitelist(Flashblock.getTargetURI(e.target))) ||
				Flashblock.blockedByContentPolicy(e.target)))
			) {
			e.preventDefault();
		}
		e.stopPropagation();
	},

	// Gets the hostname from the URI of the current page
	getHost : function () {
		var pageURI;
		if (gContextMenu)
			pageURI = gContextMenu.target.baseURI;
		else
			pageURI = content.location;

		// Work around about: and file:// URIs.
		// If we do uri.spec = "about:blank", the URI ends up as about://blank/
		if(/about:|file:|news:|snews:/i.test(pageURI.protocol))
			return null;

		var uri = Components.classes['@mozilla.org/network/standard-url;1']
			.createInstance(Components.interfaces.nsIURI);
		uri.spec = pageURI;

		// Phil: use asciiHost until we change the pref from char to complex
		var host = uri.asciiHost;
		if (uri.port > 0)
			host += ":" + uri.port;

		return host;
	},

	// Adds the host of the current URI to the whitelist
	addSiteToWhitelist : function (site) {
		var host = site || this.getHost();
		if( (!host) || (host == "") )
			return;

		var prefStr = FBlockUtils.getWhitelist();
		var re = new RegExp("(^|,)" + host + "(,|$)");
		if(! re.test(prefStr)) {
			if(prefStr && prefStr.length > 0)
				prefStr += "," + host;
			else
				prefStr = host;
			FBlockUtils.setWhitelist(prefStr);
		}
	},

	// Removes the host of the current URI from the whitelist
	removeSiteFromWhitelist : function () {
		var host = this.getHost();
		if( (!host) || (host == "") )
			return;

		var prefStr = FBlockUtils.getWhitelist();
		var regex = new RegExp("(^|,)(" + host + ")(,|$)", "g");

		prefStr = prefStr.replace(regex, "$3");
		FBlockUtils.setWhitelist(prefStr);
	},

	// Toggles the whitelist status of the host of the current URI
	toggleSiteWhitelisted : function () {
		host = this.getHost();
		if(this.checkHostInWhitelist(host))
			this.removeSiteFromWhitelist();
		else
			this.addSiteToWhitelist();
	},


/// CONTEXT MENU FUNCTIONS

    contextMenuInit : function () {
      var items = ["contentAreaContextMenu", "messagePaneContext"];
      for (var i = 0; i < items.length; i++) {
        var cm = document.getElementById(items[i]);
        if (cm)
          cm.addEventListener("popupshowing",Flashblock.contextMenu,false);
      }
      Flashblock.setButtonState(Flashblock.isEnabled());
    },

    // was flashblockContextMenu()
    contextMenu : function () {
      var cm = gContextMenu;
      var onFlash = cm.hasBGImage &&
        cm.bgImageURL.indexOf("chrome://flashblock") == 0;

      // Workaround for Mozilla Bug 482941 and Bug 422851
      if (!onFlash && (cm.target instanceof HTMLDivElement)) {
        var style = cm.target.getAttribute("style");
        if ((style != null) && style.indexOf("chrome://flashblock") >= 0)
          onFlash = true;
      }
      var nukeItem = document.getElementById("nukeanything-do-nuke");

      var itemsToShow = ["context-flashAllow", "context-flashLocation", "context-flashWhitelist"];
      for (var ii = 0; ii < itemsToShow.length; ii++) {
        cm.showItem(itemsToShow[ii], onFlash);
      }
      cm.showItem("context-flashRemove", onFlash && !nukeItem);

      if (onFlash) {

        var itemsToHide = ["context-back", "context-forward", "context-reload",
          "context-stop", "context-sep-stop",
          "context-bookmarkpage", "context-savepage", "context-sendpage",
          "context-viewbgimage", "context-viewbgimage-menu", "context-sep-viewbgimage", 
          "context-selectall", "context-viewsource", "context-viewinfo",
          "context-metadata", "context-sep-properties",
          "switchToTrident", "context-print" ];
        for (var ii = 0; ii < itemsToHide.length; ii++) {
          cm.showItem(itemsToHide[ii], false);
        }

        var thisURI = Components.classes['@mozilla.org/network/standard-url;1']
            .createInstance(Components.interfaces.nsIURI);
        thisURI.spec = gContextMenu.target.baseURI;
        document.getElementById("context-flashAllow")
          .setAttribute("tooltiptext", thisURI.prePath);

        var cmLocationItem = document.getElementById("context-flashLocation");
        if (cmLocationItem && gContextMenu.target.title) {
          cmLocationItem.setAttribute("tooltiptext",
                                      Flashblock.getAbsoluteURL(gContextMenu.target));
        }

        Flashblock.checkWhitelistToggle();
      }
    },

    getAbsoluteURL : function(target) {
        var absURL = target.title;
        if (!/^http(s?):/i.test(absURL)) {
          var ios = Components.classes["@mozilla.org/network/io-service;1"]
                              .getService(Components.interfaces.nsIIOService);
          var baseURI  = ios.newURI(target.baseURI, null, null);
          absURL = ios.newURI(baseURI.resolve(absURL), null, null).spec;
        }
        return absURL;
    },

    // was flashblockOptions()
    showOptions : function() {
        window.openDialog("chrome://flashblock/content/options.xul",
            "FlashblockOptions", "chrome,titlebar,toolbar,centerscreen,resizable");
    },

    copyLocation : function() {
      var clipboard = Components.classes["@mozilla.org/widget/clipboardhelper;1"]
                      .getService(Components.interfaces.nsIClipboardHelper);
      clipboard.copyString(Flashblock.getAbsoluteURL(gContextMenu.target));
    },

/// INITIALIZATION CODE
    onInstall : function() {
        window.removeEventListener("load", Flashblock.onInstall, true);

        // Remove the old-style userContent.css import
        Flashblock.removeImportFromUserStylesheet('userContent.css');

        // Only use the new stylesheet api
        var sss = Components.classes["@mozilla.org/content/style-sheet-service;1"]
                  .getService(Components.interfaces.nsIStyleSheetService);
        var ios = Components.classes["@mozilla.org/network/io-service;1"]
                  .getService(Components.interfaces.nsIIOService);
        var u = ios.newURI("chrome://flashblock/content/flashblock.css", null, null);
        if(!sss.sheetRegistered(u, sss.USER_SHEET)) {
          sss.loadAndRegisterSheet(u, sss.USER_SHEET);
        }
    },

    browserInit: function() {
      Flashblock.addPrefObserver();
      Flashblock.loadWhitelist();
      gFlashblockEnabled = Flashblock.isEnabled();
      gSilverblockEnabled = Flashblock.isSilverlightEnabled();
      Flashblock._whitelistTargetEnabled = Flashblock.isTargetEnabled();

      window.addEventListener("load", Flashblock.onInstall, true);
      window.addEventListener("load", Flashblock.contextMenuInit, true);
      window.addEventListener("flashblockCheckLoad", Flashblock.checkLoadFlash, true, true)
      window.addEventListener("silverblockCheckLoad", Flashblock.checkLoadSilver, true, true)
    },

/// TOOLBARBUTTON CODE

  //was flashblockToggleButton()
    toggleButton : function(event) {
        var state = !gFlashblockEnabled;
        FBlockUtils.setEnabled(state);
        Flashblock.setButtonState(state);
        if (event.metaKey || event.ctrlKey || event.shiftKey) {
            BrowserReload();
        }
    },

  //was flashblockSetButtonState(state)
    setButtonState : function(state) {
      var isJavascriptEnabled = FBlockUtils.isJavascriptEnabled();
        var button = document.getElementById("flashblockToggle-button");
        if (button) {
            button.setAttribute("state", state ? "enabled" : "disabled");
            button.setAttribute("disabled", !isJavascriptEnabled);
            button.setAttribute("label",
              button.getAttribute(state ? "labelon" :"labeloff"));
        }
        button = document.getElementById("flashblockMozToggle-button");
        if (button) {
            button.setAttribute("state", state ? "enabled" : "disabled");
            button.setAttribute("disabled", !isJavascriptEnabled);
            button.setAttribute("label",
              button.getAttribute(state ? "labelon" :"labeloff"));
        }
    },

    setTooltipSite : function() {
    var thisURI = Components.classes['@mozilla.org/network/standard-url;1']
                            .createInstance(Components.interfaces.nsIURI);
        thisURI.spec = content.location;
        var menu = document.getElementById("buttonmenu-flashblockAllow");
        if (menu) { 
            menu.setAttribute("tooltiptext", thisURI.prePath)
        };
    },

    // workaround for bug 147670
    fixParentTip : function(state, pnode) {
        var tip;
        if (state == "hide") {
            tip = pnode.getAttribute("tooltiptext");
            if (tip) {
                pnode.setAttribute("temptip", tip);
                pnode.removeAttribute("tooltiptext");
            };
            Flashblock.setTooltipSite();
        } else if (state == "show") {
            tip = pnode.getAttribute("temptip");
            if (tip) {
                pnode.setAttribute("tooltiptext", tip);
                pnode.removeAttribute("temptip");
            };
        }
    },

	checkWhitelistToggle : function () {
		var host = this.getHost();
		var toolbarWhitelistItem = document.getElementById("buttonmenu-flashblockAllow");
		var contextmenuWhitelistItem = document.getElementById("context-flashAllow");

		if(host) {
			var whitelisted = this.checkHostInWhitelist(host);
			contextmenuWhitelistItem.setAttribute("disabled", false);
			if(toolbarWhitelistItem) {
				toolbarWhitelistItem.setAttribute("disabled", false);
				toolbarWhitelistItem.setAttribute("checked", whitelisted)
			}

			if (gContextMenu) {
				var thisURI = Components.classes['@mozilla.org/network/standard-url;1']
					.createInstance(Components.interfaces.nsIURI);
				thisURI.spec = gContextMenu.target.baseURI;
				whitelisted = this.checkHostInWhitelist(thisURI.host);
				contextmenuWhitelistItem.setAttribute("checked", whitelisted);
			}
		} else {
			contextmenuWhitelistItem.setAttribute("disabled", true);
			if(toolbarWhitelistItem)
				toolbarWhitelistItem.setAttribute("disabled", true);
		}
    },

/// MISC

    //was flashblockHideObject()
    hideObject : function() {
        if(gContextMenu) {
            var obj = gContextMenu.target;
            if(obj) {
                obj.style.display = "none";
            }
        }
    },

    // the isEnabled() function in flashblock-prefs.js seems to go out of scope 
    isEnabled : function() {
        var prefs = Components.classes["@mozilla.org/preferences-service;1"]
                              .getService(Components.interfaces.nsIPrefBranch);

        if(prefs.getPrefType("flashblock.enabled") == prefs.PREF_BOOL)
            return prefs.getBoolPref("flashblock.enabled");
        return true;
    },

    isSilverlightEnabled : function() {
        var prefs = Components.classes["@mozilla.org/preferences-service;1"]
                              .getService(Components.interfaces.nsIPrefBranch);

        if(prefs.getPrefType("flashblock.silverlight.blocked") == prefs.PREF_BOOL)
            return prefs.getBoolPref("flashblock.silverlight.blocked");
        return false;
    },

    isTargetEnabled : function() {
        var prefs = Components.classes["@mozilla.org/preferences-service;1"]
                              .getService(Components.interfaces.nsIPrefBranch);

        if(prefs.getPrefType("flashblock.silverlight.blocked") == prefs.PREF_BOOL)
            return prefs.getBoolPref("flashblock.whitelist.includeTarget");
        return true;
    }
}

var gFlashblockWhitelist;
var gFlashblockEnabled;
var gSilverblockEnabled;
