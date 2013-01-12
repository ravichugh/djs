//3 downcasts cause of activex
//3 init
//un-globalled a variable
//fixed 1 inferred annot, and 2 unknown annots
//2 settimeout
function createSpeaker() /*: -> SAPISpVoice */ {
    var spv = /*:downcast SAPISpVoice*/(new ActiveXObject("SAPI.SpVoice"));
    return spv;
}

function createSpFileStream() /*:  -> SAPISpFileStream1 */ {
    var spf = /*:downcast SAPISpFileStream1*/(new ActiveXObject("SAPI.SpFileStream.1"));
    return spf;
}

function getVoiceList() /*:  -> Any */ {
    var sp = createSpeaker();
    var voiceList = sp.GetVoices();

    return voiceList;
}


function isFileNameValid(fileName) /*: Str -> Bool */ {
    if (/^[^\\\/\:\*\?\"\<\>\|\.]+(\.[^\\\/\:\*\?\"\<\>\|\.]+)*$/.test(fileName)) {
        return true;
    }
    else {
        return false;
    }
}

function getSaveFolder() /*:  -> Str + Null */ {

    var objShell = /*:downcast ShellApplication*/(new ActiveXObject("Shell.Application"));
    var objFolder = objShell.BrowseForFolder(0, "Save wav file in...", 0);

    if (objFolder != null) {
        return objFolder.self.Path;
    }
    return null;
}


// Additional Info:
// get a list of available voices from the computer...

//var voiceList = getVoiceList();   // getVoiceList() method is in this utils.js file :)
//for(var i = 0; i < voiceList.count; i++){
//	voicesLabel.innerText += "\n\n" + (i +1) + ".) " + voiceList.Item(i).GetDescription();
//}

// set a selected voice to the SpVoice object:
//  var speaker = new ActiveXObject("SAPI.SpVoice");
//  speaker.Voice = speaker.GetVoices().Item(0);
//  speaker.Speak("Hello");


// for more information, refer to :
//  http://www.microsoft.com/technet/scriptcenter/funzone/games/sapi.mspx


// for the SAPI.SpVoice , we can set Volume, Rate too:
// var speaker = new ActiveXObject("SAPI.SpVoice");
// speaker.Volume = 9;   // range from 0 to 100
// speaker.Rate = 3;     // range from -10 to 10

//////===========================================================

var speaker = /*:upcast Null + SAPISpVoice*/null;
var SSFMCreateForWrite = 3;

// SpeechVoiceSpeakFlags
var SVSFlagsAsync = 1;
var SVSFIsFilename = 4;


var isSpeakingText = false;
var checkTextSpeakingStatusToken=0;

var isReadingTextFile = false;
var checkTextFileReadingStatusToken=0;
var textFilePath = "";

function view_onOpen() /*:  -> Undef */ {}


function checkText() /*:  -> Undef */ {
    if (textbox.value.length == 0) {
        alert("Please enter some words in the text box.");
        return;
    }
}

//------------------------------------------ speak


function textbox_onchange() /*:  -> Undef */ {

    if (textbox.value.length > 0) {
        clearButton.enabled = true;
        previewButton.enabled = true;
        toWavButton.enabled = true;
    }
    else {
        clearButton.enabled = false;
        previewButton.enabled = false;
        toWavButton.enabled = false;
    }
}

function disableButtonsWhenSpeakingText() /*:  -> Undef */ {
    toWavButton.enabled = false;
    clearButton.enabled = false;
    toMainMenuButton.enabled = false;
}

function enableButtonsAfterSpeakingText() /*:  -> Undef */ {
    toWavButton.enabled = true;
    clearButton.enabled = true;
    toMainMenuButton.enabled = true;
}

function preview() /*:  -> Undef */ {
    checkText();
    speakText(textbox.value);
}

function speakText(str) /*: Str -> Undef */ {
    disableButtonsWhenSpeakingText();

    speaker = createSpeaker();
    //speaker.Voice = speaker.GetVoices().Item(1);
    speaker.Speak(str, SVSFlagsAsync);

    isSpeakingText = true;
    previewButton.caption = "Stop";

    checkTextSpeakingStatusToken = setNumerval(checkTextSpeakingStatus, 500);
}


// this function checks whether the speaking of text is finished. If it is finished, this function clear the interval and set the stop button caption to "play".


function checkTextSpeakingStatus() /*:  -> Undef */ {
    var isDone = speaker.WaitUntilDone(1);

    if (isDone) {
        previewButton.caption = "Preview voice";
        enableButtonsAfterSpeakingText();
        isSpeakingText = false;

        clearNumerval(checkTextSpeakingStatusToken);
    }
}




function toWav() /*:  -> Undef */ {
    toMainMenuButton.visible = false;
    saveTextDiv.visible = false;

    saveTextDiv2.visible = true;
}

function textDiv2_backButton_onclick() /*:  -> Undef */ {
    toMainMenuButton.visible = true;
    saveTextDiv2.visible = false;

    saveTextDiv.visible = true;
}

function saveTextToWavButton_onclick() /*:  -> Undef */ {

    saveAsWav(textbox.value);
}

// save the provided text as a wav file.


function saveAsWav(str) /*: Str -> Undef */ {
    var fileName = text_wavNameEdit.value;

    if (isFileNameValid(fileName)) {
        var pathNamespace = getSaveFolder();

        if (pathNamespace == null) {
            return;
        }
        var wavFilePath = pathNamespace + "\\" + fileName + ".wav";

        speaker = createSpeaker();
        var spFile = createSpFileStream();

        spFile.open(wavFilePath, SSFMCreateForWrite);
        speaker.AudioOutputStream = spFile;

        try {
            speaker.Speak(str, SVSFlagsAsync);
            speaker.WaitUntilDone(-1);

            spFile.Close();
            text_wavNameEdit.value = "untitled";
            alert("Wav file created.\nSaved in " + wavFilePath);
        } catch (e) {
            spFile.Close();
            alert("An error occured !. Couldn't save the wav file");
        }
    }
    else {
        alert("Please enter a valid filename.");
        return;
    }

}



//---------------------------- opening a text file


function saveFileDiv_onOpen() /*:  -> Undef */ {
    if (textFilePathEdit.value.length > 0) {
        saveFileDiv_enableButtonsForTextFile();
    }
    else {
        saveFileDiv_disableButtonsForTextFile();
    }
}

// enables read & save as wav buttons after getting the text file path.


function saveFileDiv_enableButtonsForTextFile() /*:  -> Undef */ {
    readFileButton.enabled = true;
    saveFileToWavButton.enabled = true;

    saveAsNameEdit_onchange();
}

// disables read & save as wav buttons if no text file is selected.


function saveFileDiv_disableButtonsForTextFile() /*:  -> Undef */ {
    readFileButton.enabled = false;
    saveFileToWavButton.enabled = false;
}

function openFile() /*:  -> Undef */ {
    textFilePath = framework.BrowseForFile("Text Files|*.txt");

    if (textFilePath.length == 0) {
        saveFileDiv_onOpen();
    }
    else {
        textFilePathEdit.value = textFilePath;
        saveFileDiv_enableButtonsForTextFile();
    }
}


function disableButtonsWhenReadingTextFile() /*:  -> Undef */ {
    openButton.enabled = false;
    saveFileToWavButton.enabled = false;
    toMainMenuButton.enabled = false;
}

function enableButtonsAfterReadingTextFile() /*:  -> Undef */ {
    openButton.enabled = true;
    saveFileToWavButton.enabled = true;
    toMainMenuButton.enabled = true;
}

// read a selected text file.


function readTextFile(filePath) /*: Str -> Undef */ {
    disableButtonsWhenReadingTextFile();

    speaker = createSpeaker();
    speaker.Speak(filePath, SVSFlagsAsync + SVSFIsFilename);

    readFileButton.caption = "Stop";
    isReadingTextFile = true;

    checkTextFileReadingStatusToken = setNumerval(checkTextFileReadingStatus, 500);

}


// this function checks whether the reading of text file is finished.
// If it is finished, this function clear the interval and set the stop button caption to "play".


function checkTextFileReadingStatus() /*:  -> Undef */ {
    var isDone = speaker.WaitUntilDone(1);

    if (isDone) {
        enableButtonsAfterReadingTextFile();
        readFileButton.caption = "Read File";
        isReadingTextFile = false;

        clearNumerval(checkTextFileReadingStatusToken);
    }
}

// save the selected text file in wav format.


function saveTextFileAsWav(textFilePath) /*: Str -> Undef */ {
    var fileName = saveAsNameEdit.value;

    if (isFileNameValid(fileName)) {
        var pathNamespace = getSaveFolder();

        if (pathNamespace == null) {
            return;
        }

        speaker = createSpeaker();
        var spFile = createSpFileStream();

        var wavFilePath = pathNamespace + "\\" + fileName + ".wav";

        spFile.open(wavFilePath, SSFMCreateForWrite);
        speaker.AudioOutputStream = spFile;

        try {
            speaker.Speak(textFilePath, SVSFlagsAsync + SVSFIsFilename);
            speaker.WaitUntilDone(-1);

            spFile.Close();
            saveAsNameEdit.value = "untitled";
            alert("Wav file created.\nSaved in " + wavFilePath);
        } catch (e) {
            spFile.Close();
            alert("An error occured !. Couldn't save the wav file");
        }
    }
    else {
        alert("Please enter a valid filename.");
        return;
    }
}



//----------------------------------------------------------------- functions for buttons

function toMainMenuButton_onclick() /*:  -> Undef */ {
    if (saveTextDiv.visible) {
        saveTextDiv.visible = false;
    }

    if (saveFileDiv.visible) {
        saveFileDiv.visible = false;
    }

    hideButtons_top();
    mainMenuDiv.visible = true;
}


function showButtons_top() /*:  -> Undef */ {
    toMainMenuButton.visible = true;
    logoImg_big.visible = false;
    logoImg_small.visible = true;
}

function hideButtons_top() /*:  -> Undef */ {
    toMainMenuButton.visible = false;
    logoImg_big.visible = true;
    logoImg_small.visible = false;
}


// buttons in saveTextDiv


function previewButton_onclick() /*:  -> Undef */ {
    if (isSpeakingText) {
        stopSpeaking();
    }
    else {
        preview();
    }
}

function stopSpeaking() /*:  -> Undef */ {
    speaker.Pause();
    speaker.AudioOutputStream = null;
    speaker = null;

    clearNumerval(checkTextSpeakingStatusToken);

    enableButtonsAfterSpeakingText();
    previewButton.caption = "Preview voice";
    isSpeakingText = false;
}

function toWavButton_onclick() /*:  -> Undef */ {
    toWav();
}

function clearButton_onclick() /*:  -> Undef */ {
    textbox.value = "";
    textbox.focus();
}

function saveTextButton_onclick() /*:  -> Undef */ {
    mainMenuDiv.visible = false;

    showButtons_top();
    textbox_onchange();
    saveTextDiv.visible = true;
    textbox.focus();
}


// buttons in saveFileDiv


function openButton_onclick() /*:  -> Undef */ {
    openFile();
}

function saveFileButton_onclick() /*:  -> Undef */ {
    mainMenuDiv.visible = false;

    showButtons_top();
    saveFileDiv_onOpen();
    saveFileDiv.visible = true;
}

function readFileButton_onclick() /*:  -> Undef */ {

    if (isReadingTextFile) {
        stopReadingTextFile();
    }
    else {
        readTextFile(textFilePath);
    }
}

function stopReadingTextFile() /*:  -> Undef */ {
    speaker.Pause();
    speaker.AudioOutputStream = null;
    speaker = null;

    enableButtonsAfterReadingTextFile();
    clearNumerval(checkTextFileReadingStatusToken);

    readFileButton.caption = "Read File";
    isReadingTextFile = false;
}

function saveFileToWavButton_onclick() /*:  -> Undef */ {
    saveTextFileAsWav(textFilePath);
}




function text_wavNameEdit_onchange() /*:  -> Undef */ {
    if (text_wavNameEdit.value.length > 0) {
        saveTextToWavButton.enabled = true;
    }
    else {
        saveTextToWavButton.enabled = false;
    }

}



function saveAsNameEdit_onchange() /*:  -> Undef */ {
    if (saveAsNameEdit.value.length == 0) {
        saveFileToWavButton.enabled = false;
        return;
    }
    if (textFilePathEdit.value.length > 0) {
        if (saveAsNameEdit.value.length > 0) {
            saveFileToWavButton.enabled = true;
        }
    }
}
