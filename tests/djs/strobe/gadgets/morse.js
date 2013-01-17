//4 vars added
//5 init i to 0 instead of undefined
//4 changes to settimeout to not use a string
var token /*: Int */ = 0; //CLAUDIU: move here for func lift

var edit1 = /*: lEdit1 */ {};
var edit2 = /*: lEdit2 */ { value: ""};
var bplay = /*: lBplay */ {};
var radio2 = /*: lRadio2 */ {};


/*: #define tyEdit  
    () / (  lEdit1: Dict > lObjPro,
            lEdit2: Dict > lObjPro,
            lBplay: Dict > lObjPro
         ) -> Top / sameType 
*/ "#define";

/*: tyDValueS {"value": Str} > lObjPro */ "#define";
/*: tyDValueB {"value": Bool} > lObjPro */ "#define";


//PV: added these
var clearTimeout  = function(i) /*:(i:Int) / () -> Top / sameType */ {};
var alert         = function(s) /*:(s:Str) / () -> Top / sameType */ {};

var view_onOpen = function() /*: tyEdit */ {
    edit1.value = "Type the text...";
    edit2.value = "- -.-- .--. . + - .... . + - . -..- - .-.-.- .-.-.- .-.-.- ";
    edit2.readonly = true;
    bplay.visible = true;
    edit2.bold = true;
    edit2.size = 12;
};

var radio1_onclick = function() /*: tyEdit */ {
    edit1.value = "";
    edit2.value = "";
    bplay.visible = true;
    bplay.caption = "Play";
    edit2.bold = true;
    edit2.size = 12;
};


//PV: rearranged
var stopAudio = function()  /*: () / () -> Top / sameType */ {
    for (var i /*: Int */ = 1; i <= token; i++)
    clearTimeout(i);
};



var radio2_onclick = function()  /*: tyEdit */ { 
    stopAudio();
    edit1.value = "";
    edit2.value = "";
    bplay.visible = false;
    edit2.bold = false;
    edit2.size = 10;
};


 /*: writeText:: (s: Str) / (lEdit2: tyDValueS ) -> Top / sameType */ "#type"; 
//PV: rearranged
var writeText = function(s)
{
    var output = edit2;
    
    //PV: Adding this just to type check
    if (s === '.-') {
      output.value += "a";
    }
    else if (s === '-...') {
      output.value += "b";
    }


    //TODO: this switch statement still not working
    //switch (s) {
    //case '.-':
    //    output.value = output.value + "a";
    //    break;
    //case '-...':
    //    output.value = output.value + "b";
    //    break;
    //case '-.-.':
    //    output.value = output.value + "c";
    //    break;
    //case '-..':
    //    output.value += "d";
    //    break;
    //case '.':
    //    output.value += "e";
    //    break;
    //case '..-.':
    //    output.value += "f";
    //    break;
    //case '--.':
    //    output.value += "g";
    //    break;
    //case '....':
    //    output.value += "h";
    //    break;
    //case '..':
    //    output.value += "i";
    //    break;
    //case '.---':
    //    output.value += "j";
    //    break;
    //case '-.-':
    //    output.value += "k";
    //    break;
    //case '.-..':
    //    output.value += "l";
    //    break;
    //case '--':
    //    output.value += "m";
    //    break;
    //case '-.':
    //    output.value += "n";
    //    break;
    //case '---':
    //    output.value += "o";
    //    break;
    //case '.--.':
    //    output.value += "p";
    //    break;
    //case '--.-':
    //    output.value += "q";
    //    break;
    //case '.-.':
    //    output.value += "r";
    //    break;
    //case '...':
    //    output.value += "s";
    //    break;
    //case '-':
    //    output.value += "t";
    //    break;
    //case '..-':
    //    output.value += "u";
    //    break;
    //case '...-':
    //    output.value += "v";
    //    break;
    //case '.--':
    //    output.value += "w";
    //    break;
    //case '-..-':
    //    output.value += "x";
    //    break;
    //case '-.--':
    //    output.value += "y";
    //    break;
    //case '--..':
    //    output.value += "z";
    //    break;
    //case '-----':
    //    output.value += "0";
    //    break;
    //case '.----':
    //    output.value += "1";
    //    break;
    //case '..---':
    //    output.value += "2";
    //    break;
    //case '...--':
    //    output.value += "3";
    //    break;
    //case '....-':
    //    output.value += "4";
    //    break;
    //case '.....':
    //    output.value += "5";
    //    break;
    //case '-....':
    //    output.value += "6";
    //    break;
    //case '--...':
    //    output.value += "7";
    //    break;
    //case '---..':
    //    output.value += "8";
    //    break;
    //case '----.':
    //    output.value += "9";
    //    break;
    //case '.-.-.-':
    //    output.value += ".";
    //    break;
    //case '--..--':
    //    output.value += ",";
    //    break;
    //case '..--..':
    //    output.value += "?";
    //    break;
    //case '-.-.--':
    //    output.value += "!";
    //    break;
    //case '-..-.':
    //    output.value += "/";
    //    break;
    //case '-.--.':
    //    output.value += "(";
    //    break;
    //case '-.--.-':
    //    output.value += ")";
    //    break;
    //case '---...':
    //    output.value += ";";
    //    break;
    //case '-.-.-.':
    //    output.value += ";";
    //    break;
    //case '-...-':
    //    output.value += "=";
    //    break;
    //case '.-.-.':
    //    output.value += "+";
    //    break;
    //case '-....-':
    //    output.value += "-";
    //    break;
    //case '..--.-':
    //    output.value += "_";
    //    break;
    //default:
    //    break;
    //}
};


/*: NonNeg {Int | (>= v 0)} */ "#define";

//PV: rearranged
var code2Text = function code2Text_rec() 
/*: () / (lEdit2: tyDValueS, lEdit1: tyDValueS) -> Top / sameType */
{
    var input = edit1.value;
    var output = edit2,
        s= "";
    //assert(/*: Str */ (input));   //PV: added this

    var len = input.length,
        i=0, comb /*: Str */ = "";
    
    //assert(/*: Int */ (len)); //PV: added this 
    //assert(/*: Str */ (output.value)); //PV: added this 

    output.value = "";
    if (len < 4000) {
            /*: (&i: NonNeg, &s: Str, &comb: Str, lEdit1: tyDValueS, lEdit2: tyDValueS)
              -> (&i: sameType, &s:sameType, lEdit1: sameType, lEdit2: sameType, &comb: sameType) */
            for (i = 0; i < len; i++) {
                if (input.charAt(i) != '.' && input.charAt(i) != '-' && input.charAt(i) != '+' && input.charAt(i) != ' ') {
                    s = input;
                    edit1.value = "";

                    /*: (lEdit1: tyDValueS) -> sameType */
                    for (var j /*: NonNeg*/ = 0; j <= s.length; j++) {
                        if (s.charAt(j) == '.' || s.charAt(j) == '-' || s.charAt(j) == '+' || s.charAt(j) == ' ') {
                            edit1.value += s.charAt(j);
                        }
                    }
                    //alert("This is not a valid Morse Code. It should contain only .-+ and the character \"space\"");
                    //PV: Had to change this to rec 
                    code2Text_rec();
                    return;
                }
                if (input.charAt(i) != ' ') {
                    if (input.charAt(i) != '.' || input.charAt(i) != '-' || input.charAt(i) != '+') if (input.charAt(i) == '+') output.value += " ";
                    else comb = comb + input.charAt(i);
                }
                else {
                    writeText(comb);
                    comb = "";
                }
            }
        }
    else output.value = "The code is too large...";
};


//PV: rearranged this
var writeCode = function(c)  /*: (c:Str) / (lEdit2: tyDValueS) -> Top / (lEdit2: sameType) */ {
    var output = edit2;
  
    if (c == 'a') {
      output.value += ".-";
    };

//TODO: switch statement kept commented for the time being 
//    switch (c) {
//    case 'a':
//        output.value += ".- ";
//        break;
//    case 'b':
//        output.value += "-... ";
//        break;
//    case 'c':
//        output.value += "-.-. ";
//        break;
//    case 'd':
//        output.value += "-.. ";
//        break;
//    case 'e':
//        output.value += ". ";
//        break;
//    case 'f':
//        output.value += "..-. ";
//        break;
//    case 'g':
//        output.value += "--. ";
//        break;
//    case 'h':
//        output.value += ".... ";
//        break;
//    case 'i':
//        output.value += ".. ";
//        break;
//    case 'j':
//        output.value += ".--- ";
//        break;
//    case 'k':
//        output.value += "-.- ";
//        break;
//    case 'l':
//        output.value += ".-.. ";
//        break;
//    case 'm':
//        output.value += "-- ";
//        break;
//    case 'n':
//        output.value += "-. ";
//        break;
//    case 'o':
//        output.value += "--- ";
//        break;
//    case 'p':
//        output.value += ".--. ";
//        break;
//    case 'q':
//        output.value += "--.- ";
//        break;
//    case 'r':
//        output.value += ".-. ";
//        break;
//    case 's':
//        output.value += "... ";
//        break;
//    case 't':
//        output.value += "- ";
//        break;
//    case 'u':
//        output.value += "..- ";
//        break;
//    case 'v':
//        output.value += "...- ";
//        break;
//    case 'w':
//        output.value += ".-- ";
//        break;
//    case 'x':
//        output.value += "-..- ";
//        break;
//    case 'y':
//        output.value += "-.-- ";
//        break;
//    case 'z':
//        output.value += "--.. ";
//        break;
//    case '0':
//        output.value += "----- ";
//        break;
//    case '1':
//        output.value += ".---- ";
//        break;
//    case '2':
//        output.value += "..--- ";
//        break;
//    case '3':
//        output.value += "...-- ";
//        break;
//    case '4':
//        output.value += "....- ";
//        break;
//    case '5':
//        output.value += "..... ";
//        break;
//    case '6':
//        output.value += "-.... ";
//        break;
//    case '7':
//        output.value += "--... ";
//        break;
//    case '8':
//        output.value += "---.. ";
//        break;
//    case '9':
//        output.value += "----. ";
//        break;
//    case '.':
//        output.value += ".-.-.- ";
//        break;
//    case ',':
//        output.value += "--..-- ";
//        break;
//    case '?':
//        output.value += "..--.. ";
//        break;
//    case '!':
//        output.value += "-.-.-- ";
//        break;
//    case '/':
//        output.value += "-..-. ";
//        break;
//    case '(':
//        output.value += "-.--. ";
//        break;
//    case ')':
//        output.value += "-.--.- ";
//        break;
//    case ':':
//        output.value += "---... ";
//        break;
//    case ';':
//        output.value += "-.-.-. ";
//        break;
//    case '=':
//        output.value += "-...- ";
//        break;
//    case '+':
//        output.value += ".-.-. ";
//        break;
//    case '-':
//        output.value += "-....- ";
//        break;
//    case '_':
//        output.value += "..--.- ";
//        break;
//    case ' ':
//        output.value += "+ ";
//        break;
//    default:
//        break;
//    }
};



//PV: rearranged this
var text2Code = function() /*: () / (lEdit1: tyDValueS, lEdit2: tyDValueS) -> Top / (lEdit1: sameType, lEdit2: sameType) */ {
    var possiblecomb = "abcdefghijklmnopqrstuvwxyz0123456789.,?!/():;=+-_";
    var input /*: Str */ = edit1.value.toLowerCase();
    var output = edit2;
    if (input.length > 1000) //max 1000 characters
    {
        output.value = "The text is too large...";
    }
    else {
        output.value = "";
        /*: (lEdit2: tyDValueS) -> (lEdit2: sameType) */
        for (var i /*: NonNeg */ = 0; i < input.length; i++)
        writeCode(input.charAt(i));
    }
};

var edit1_onchange = function() 
/*: () / (lEdit1: tyDValueS, lEdit2: tyDValueS, lRadio2: tyDValueB) -> Top / (lEdit1: sameType, lEdit2: sameType, lRadio2: sameType) */
{
    if (radio2.value == true) {} //code2Text();    //TODO: code2Text does not type check -- FIX IT!
    else text2Code();
};

var edit1_onclick = function() /*: () / (lEdit1: tyDValueS, lEdit2: tyDValueS) -> Top / sameType */  {
    if (edit1.value == "Type the text...") {
        edit1.value = "";
        edit2.value = "";
    }
};


//PV: start of added definitions
var play_d = /*: lPlay */ {
  play: function() 
  /*: () / (&framework: Ref(lFramework)) -> Top / (&framework: sameType)*/ 
  {return; }
};


var framework = /*: lFramework  */ { 
  audio: /*: lAudio */ { 
    open: function(s) 
      /*: (s: Str) / (&framework: Ref(lFramework))-> 
        Ref(lPlay) / (&framework: sameExact) */ {
        return play_d;} 
    }
};

var storage = /*: lStorage */ { 
  extract: function(s) /*: (s:Str) -> Str */ { return "";}
};

//setTimeout() method calls a function or evaluates an expression after a specified number of milliseconds.
var setTimeout = function(f, i) /*:  [A,B] (f: {(v::(x:A) -> B)}, i: A) / () -> B / sameType */
 {return f(i); };
//PV: end of added definitions


//TODO: If you add "lEdit2: tyDValueS" to the input heap then it fails

var playAudio = function() /*: () / (lAudio:   {"open"    : {(v:: (s:Str) -> Ref(lPlay))}} > lObjPro,
                                     lPlay:    {"play"    : {(v:: (     ) -> Top       )}} > lObjPro,
                                     &framework: fw0: Ref(lFramework)
                                    )
                             -> Top / (lAudio: sameType, lPlay: sameType, &framework: Ref(lFramework) ) */  {

    assert(/*: Str */ (edit2.value));
                               
    var source = edit2.value,
        i /*: NonNeg */ = 0;

    var audio_dit = framework.audio.open("a");
//    var audio_dit = framework.audio.open(storage.extract("dit.wav"));
//    var audio_dah = framework.audio.open(storage.extract("dah.wav"));
//    var audio_pause = framework.audio.open(storage.extract("pause.wav"));
                  
    assert(/*: () -> Top */ (audio_dit.play()));


    //if (source.length != 0) {      
    
    //        [> ( &storage: Ref(lStorage), lStorage: {"extract": (s:Str) -> Str} > lObjPro, 
    //            &edit2: Ref(lEdit2), lEdit2: tyDValueS, &framework: fw1: Ref(lFramework), lFramework: {"audio": Ref(lAudio)} > lObjPro )
    //         -> (&storage: sameType, lStorage: sameType, &edit2: sameType, lEdit2: sameType, &framework: sameType, lFramework: sameType) */ 

    //        for (i = 0; i < source.length; i++) {
    //          //PV: changing switch to if...
    //            if (source.charAt(i) == '.') {
    //            //case '.':
                  
    //              //TODO: PV: changed explicit function parameter, because I was
    //              //getting: Fatal error: exception Failure("shouldn't get 
    //              //here: unannotated FuncExr")

    //              assert(/*: () -> Top */ (audio_dit.play()));

    //              //  var tmp = function() [>: () -> Top <] { audio_dit.play(); };
    //              //token = setTimeout(tmp, i * 500);
    //              //break;
    //            }
    ////        //    else if (source.charAt(i) == '-') {
    //        //    //case '-':
    //        //        var tmp = function() { audio_dah.play(); };
    //        //        token = setTimeout(tmp, i * 500);
    //        //        //break;
    //        //    }
    //        //    else {
    //        //    //default:
    //        //        var tmp = function() { audio_pause.play(); };
    //        //        token = setTimeout(tmp, i * 500);
    //        //        //break;
    //        //    }
    //        }
//            var tmp = function() { bplay.caption = "Play"; };
//            token = setTimeout(tmp, source.length * 500);
     //}
};

//var bplay_onclick = function() [>: () / (lEdit2: tyDValueS, lBplay: {"caption": Str} > lObjPro) -> Top / sameType <] {
//    if (edit2.value.length != 0) {
//        if (bplay.caption == "Play") {
//            bplay.caption = "Stop";
//            playAudio();
//        }
//        else {
//            stopAudio();
//            bplay.caption = "Play";
//        }
//    }
//}



//codes a character and appends it to output



//Text to Morse code var  = function[Max 1000 characters]



//decodes a morse combination and appends it to output


//Morse to Text var  = function[MAX 4000 characters]



