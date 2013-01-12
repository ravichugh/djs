/* TODO list *****
 + make system idle delay the breaks (assumption is that they are not working when computer is idle)
 + have notification pop-ups instead of alerts
 + take break now button that appears over time left till break text
 + add random tips/stretches instead of countdown in notification area
 - spanish
 - german

******************/
var debug = false; // FIX: 0 -> false

var bTimer = 0, secTimer = 0; //FIX: = 0

function setDefaultOptions() /*: -> Undef */
{
    // FIX: this used to use setters and broke with "expected l-value"
    options.putDefaultValue("breakNumerval", 35); //35 min
    options.putDefaultValue("microNumerval", 10); //10 min
    options.putDefaultValue("breakDuration", 240);//sec
    options.putDefaultValue("microDuration", 30); //sec
    options.putDefaultValue("idleMin", 3); //sec
    options.putDefaultValue("useTimeout", 1); //true.
    options.putDefaultValue("allowPostpone", 1); //true
    options.putDefaultValue("postponeTime",  2); //min
}

setDefaultOptions();
var bCount = /*:downcast Num */(options.getValue("breakNumerval")); // FIX: getters/setters
var mCount = /*:downcast Num */(options.getValue("microNumerval"));


function smallestCount() /*: -> Num */ // FIX: we do not lift functions
{
	if(bCount < mCount) return bCount;
	else return mCount;
}

var smCount = smallestCount();
var minimized = false;

var oneSec = debug ? 100 : 1000; // FIX: we do not do the style below
var secTime = debug ? 20 * oneSec : 60 * oneSec;
/* if(debug) 
{	
	var oneSec = 100; //1000 ms
	var secTime = 20 * oneSec; //in ms (60000)
}
else
{
	var oneSec = 1000; //1000 ms
	var secTime = 60 * oneSec; //in ms (60000)
} */
var secBar = 100; // # of ticks in bar
var cursor = framework.system.cursor.position;
var idleCycles = 0; // in min
var newItem = ContentItem(); // TODO: should say new ContentItem
//set max items
pluginHelper.max_content_items = 1;  

var tips = [tiprest1, tiprest2, tiprest3, tiprest4, tiprest5, tiprest6,
            tiprest7, tiprest8, tiprest9, tiprest10 ];

function onUnload() /*: -> Undef */
{
	stop();
}

function viewOnOpen() /*: -> Undef */
{
	setLabels();
	bTimer = setNumerval( updateCount, secTime );
	updateCountText();
	bCount--; //first timer fire (in 1 sec) will display decremented value
	mCount--;
	//sizeBar();
}

function updateCount() /*: -> Undef */
{
	updateCountText();
	smCount = smallestCount();
	if(minimized) dispInCaption();
	if(bCount <= 0)
	{
            bCount = /*:downcast Num*/(options.getValue("breakNumerval"));  // needs to be above the showAlert() since a break can be declined
		var title = RBreak;
		var desc  = takeRBreak;
		showAlert(title, desc, /*:downcast Num*/(options.getValue("breakDuration")));
		mCount = /*:downcast Num*/(options.getValue("microNumerval"));  // reset micro time, so it doesnt happen right after a long break
		updateCountText();
	}
	if(mCount <= 0)
	{
		var title = MBreak;
		var desc  = takeMBreak;
		showAlert(title, desc, /*:downcast Num */(options.getValue("microDuration")));
		mCount = /*:downcast Num*/(options.getValue("microNumerval"));
		if(mCount >= bCount)
		{
			mCount = mCount + bCount; //resume micro breaks after full break
		}
		updateCountText();
	}
	if(!(/*:downcast Bool */(options.getValue("useTimeout"))) || userActive() || debug) // only decrement if the user is active or timeout not used
	{
		bCount--;
		mCount--;
	}
}

function updateCountText() /*: -> Undef */
{
    bcount.innerText = bCount.toStr() + " " + minText;
    mcount.innerText = mCount.toStr() + " " + minText;
}

function userActive() /*: -> Bool */
{
	if((cursor.x == framework.system.cursor.position.x) && (cursor.y == framework.system.cursor.position.y)) // mouse idle
	{
            if(idleCycles < /*:downcast Num*/(options.getValue("idleMin")))
		{
			idleCycles++;
			return true;
		}
		else return false;
	}
	else // mouse moved
	{
		cursor = framework.system.cursor.position;
		idleCycles = 0;
		return true;
	}
}

function displayOptions() /*: -> Undef */
{
	microtitlelbl.innerText = microtitletxt;
	resttitlelbl.innerText = resttitletxt;
	microdurationlbl.innerText = durationtxt;
	restdurationlbl.innerText = durationtxt;
	microtimelbl.innerText = breaktimetxt;
	resttimelbl.innerText = breaktimetxt;
	dontcountlbl.innerText = dontcounttxt;
	allowpostponelbl.innerText = allowpostponetxt;
	mintxt1.innerText = minText;
	mintxt2.innerText = minText;
	mintxt3.innerText = minText;
	sectxt1.innerText = secText;
	sectxt2.innerText = secText;


	bTime.value = /*:downcast Num*/(options.getValue("breakNumerval")).toStr();
	mTime.value = /*:downcast Num*/(options.getValue("microNumerval")).toStr();	
	bDuration.value = /*:downcast Num*/(options.getValue("breakDuration")).toStr();
	mDuration.value = /*:downcast Num*/(options.getValue("microDuration")).toStr();
	usetimeout.value = /*:downcast Bool*/(options.getValue("useTimeout"));
	allowpostpone.value = /*:downcast Bool*/(options.getValue("allowPostpone"));
        postponetime.value = /*:downcast Num*/(options.getValue("postponeTime")).toStr();
}

function updateOptions() /*: -> Undef */
{
    options.putValue("breakNumerval", parseNum(bTime.value));
    options.putValue("microNumerval", parseNum(mTime.value));
    options.putValue("breakDuration", parseNum(bDuration.value));
    options.putValue("microDuration", parseNum(mDuration.value));
    options.putValue("useTimeout", usetimeout.value);
    options.putValue("allowPostpone", allowpostpone.value);
    options.putValue("postponeTime", parseNum(postponetime.value));
}

function showAlert(title, desc, time) /*: Str * Str * Num -> Undef */
{
	clearNumerval(bTimer);
	if(time == /*:downcast Num*/ (options.getValue("microDuration"))) alert(title); //microbreak
	else if(/*:downcast Bool*/(options.getValue("allowPostpone")))
	{
		if(!confirm(willTakeBreak + " " + /*:downcast Num*/(options.getValue("postponeTime")) + " " + minText + ")")) //postpone the rest break
		{
			bCount = /*:downcast Num*/(options.getValue("postponeTime")); //postpone
			mCount += /*:downcast Num*/(options.getValue("postponeTime")); //push back micro too
			updateCountText();
			bTimer = setNumerval( updateCount, secTime );
			return;
		}
		//else take the rest break
	}
	else
	{
		alert(title);
	}

	configureBar(title, desc, time);

	if(!debug) newItem.heading = title;
	if(!debug) newItem.snippet = desc;
	//newItem.notifier_image = "full.gif";
	if(!debug) cnArea.addContentItem(newItem, gddItemDisplayAsNotification);
	//cnArea.removeContentItem(newItem);
	if(!debug) cnArea.removeAllContentItems();
}

function configureBar(title, desc, time) /*: Str * Str * Num -> Undef */
{
	progbar.enabled = true;
	progbar.visible = true;
	breakcount.visible = true;
	breakcount.innerText = title;

	mnowbutton.visible = false;
	rnowbutton.visible = false;

	secBar = time;
	progbar.max = time;
	progbar.value = time;
	secTimer = setNumerval(updateBar, oneSec);
}

function updateBar() /*: -> Undef */
{
	if(secBar <= 0) 
	{
		stopBar();
		return;
	}
	else secBar--;
	if(minimized) dispInCaption();
	progbar.value = secBar;

//update the notification window
	if(secBar%(/*:downcast Num*/(options.getValue("microDuration"))-1) == 0)
	{
		newItem.snippet = randNotification(secBar);
		if(debug) alert(newItem.snippet);
		if(!debug) cnArea.addContentItem(newItem, gddItemDisplayAsNotification);
		if(!debug) cnArea.removeAllContentItems();
	}
}

function stopBar() /*: -> Undef */
{
	clearNumerval(secTimer);
	bTimer = setNumerval( updateCount, secTime );
	progbar.enabled =false;
	progbar.visible = false;
	breakcount.visible = false;

	mnowbutton.visible = true;
	rnowbutton.visible = true;

}

function randNotification(timeLeft) /*: Num -> Str */
{
	if(timeLeft == 0) return backToWorkText;
	else
	{
		var ranNum= Math.floor(Math.random()*tips.length);
		return tips[ranNum];		
	}
}

function dispInCaption() /*: -> Undef */
{
	if(smCount == 0)
	{
		if(secBar == 0) view.caption = backToWorkText;
		else view.caption = breakText + " " + secBar;
	}
	else view.caption = smCount + " " + minText;
	minimized = true;
}

function dispFull() /*: -> Undef */
{
	view.caption = GADGET_NAME;
	minimized = false;
}

function stop() /*: -> Undef */
{
	clearNumerval(bTimer);
	clearNumerval(secTimer);
}

function sizeBar() /*: -> Undef */
{
	progbar.width = view.width;
	progbar.height = view.height;
}

function toggleAllowPostpone() /*: -> Undef */
{
	if(allowpostpone.value) postponetime.enabled = true;
	else postponetime.enabled = false;

}

function mouseOverNow(button, on) /*: Num * Bool -> Undef */
{
	if(on)
	{
		if(button == 1) rnowbuttontext.visible = true;
		else if(button == 2) mnowbuttontext.visible = true;
	}
	else
	{
		if(button == 1) rnowbuttontext.visible = false;
		else if(button == 2) mnowbuttontext.visible = false;		
	}
}

function earlyBreak(type) /*: Num -> Undef */
{
	clearNumerval(bTimer);
	if(type == 1) mCount = 0;
	else bCount = 0;
	updateCount();
}

function setLabels() /*: -> Undef */
{
	nextmicrobreak.innerText = nextmicrobreakin;
	nextfullbreak.innerText = nextfullbreakin;
	rnowbuttontext.innerText =  takeitnow;
	mnowbuttontext.innerText = takeitnow;
}
