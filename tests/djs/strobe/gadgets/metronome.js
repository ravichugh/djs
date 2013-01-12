/* Eval: required 1 upcast, 1 downcast, changing null to false/0 (other
 *   sentinel values), and just 2 function annotations. not bad!
 */
var curAudioClip_ = /*:upcast Audioclip + Undef*/ undefined;
var timer = 0; // Arjun: null --> 0
var flag = 0;
var bpm = 0;
var AUDIO_CLIP_URI = "tick.wav";

function on_viewOpen() /*: -> Undef */ {
  options.putDefaultValue("bpm",100);
  bpm = /*:downcast Num */(options.getValue("bpm"));
  bpm_display.innerText = bpm.toStr();
  //pluginHelper.onAddCustomMenuItems = onAddCustomMenuItems;
}

function onAddCustomMenuItems(menu) /*: Menu -> Undef */ {
  menu.AddItem("More Gadgets", 0, onMoreGadgetsClick);
}

function onMoreGadgetsClick(_ /* Arjun: ignored arg */) /*: { } -> Undef */ {
	framework.openURL("http://www.gdgadgets.com");
}

function onStart() /*: -> Undef */ {
  if(flag == 0) {
    onStop();
    var time = parseNum((60/bpm)*1000.0, undefined);
    timer = setNumerval(onPlay,time);
    btn.image = "stop.png";
    btn.overImage = "stop_over.png";
    btn.downImage = "stop_over.png";
    flag = 1;
  }
  else {
    onStop();
    btn.image = "play.png";
    btn.overImage = "play_over.png";
    btn.downImage = "play_over.png";
    flag = 0;
  }
}

function onStop() /*: -> Undef */ {
  if(timer != 0) { // Arjun: null --> 0
    clearNumerval(timer);
    timer = 0;
  }
}

function incr() /*: -> Undef */ {
  if(280 > bpm) {
    bpm++;
    options.putValue("bpm",bpm);
    bpm_display.innerText = bpm.toStr();
    if(flag == 1) {
      flag = 0;
      onStart();
    }
  }
}

function decr() /*: -> Undef */ {
  if(60 < bpm) {
    bpm-=1;
    options.putValue("bpm",bpm);
    bpm_display.innerText = bpm.toStr();
    if(flag == 1) {
      flag = 0;
      onStart();
    }
  }
}

function onPlay() /*: -> Undef */ {
  if (typeof curAudioClip_ === "undefined") {      // Not playing anything
    curAudioClip_ = framework.audio.play(AUDIO_CLIP_URI, onAudioStateChange);
    startedAudio();
  } else {                  // Already playing something
    curAudioClip_.stop();
    curAudioClip_ = undefined; // Claudiu: null -> undefined
    stoppedAudio();
  }
}

function onAudioStateChange(audioClip, state) /*: Audioclip * Num -> Undef */ {
  if (state == gddSoundStateStopped) {
    stoppedAudio();
    curAudioClip_ = undefined; // Claudiu: null -> undefined
  } else if (state == gddSoundStatePlaying) {
    startedAudio();
  }
}

function startedAudio() /*: -> Undef */ {
  status_image.src = "green.png";
}

function stoppedAudio() /*: -> Undef */ {
  status_image.src = "red.png";
}

function check_key() /*: -> Undef */ {
  // Claudiu: keycode --> keyCode
  if(event.keyCode == 45)
    decr();
  if(event.keyCode == 43)
    incr();
}
