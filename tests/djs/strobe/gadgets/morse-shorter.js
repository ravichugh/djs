var token /*: Int */ = 0; //CLAUDIU: move here for func lift

var edit1  /*: Ref {value:Str} */ = {};
var edit2  /*: Ref {value:Str, readonly:Bool, visible:Bool} */ = {};
var bplay  /*: Ref {caption:Str, visible:Bool} */ = {};
var radio2 /*: Ref {value:Bool } */ = {};


/*: tyDValueS {"value": Str} > lObjPro */ "#define";
/*: tyDValueB {"value": Bool} > lObjPro */ "#define";


//PV: added these
var clearTimeout  = function(i) /*: (Int) -> Top */ {};
var alert         = function(s) /*: (Str) -> Top */ {};

var view_onOpen = function() /*: () -> Top */ {
    edit1.value = "Type the text...";
    edit2.value = "- -.-- .--. . + - .... . + - . -..- - .-.-.- .-.-.- .-.-.- ";
    edit2.readonly = true;
    bplay.visible = true;
    edit2.bold = true;
    edit2.size = 12;
};

var radio1_onclick = function() /*: () -> Top */ {
    edit1.value = "";
    edit2.value = "";
    bplay.visible = true;
    bplay.caption = "Play";
    edit2.bold = true;
    edit2.size = 12;
};


//PV: rearranged
var stopAudio = function()  /*: () -> Top */ {
    for (var i /*: Int */ = 1; i <= token; i++)
    clearTimeout(i);
};



var radio2_onclick = function()  /*: () -> Top */ { 
    stopAudio();
    edit1.value = "";
    edit2.value = "";
    bplay.visible = false;
    edit2.bold = false;
    edit2.size = 10;
};



//PV: rearranged
var writeText = function(s) /*: (Str) -> Top */ 
{
    var output = edit2;
    
    switch (s) {
    case '.-':
        edit2; //rkc: adding a syntactic occurrence of edit2 so that DJS
               // infers the heap annotations for &edit2 and ledit2
        output.value += "a";
        break;
    case '-...':
        output.value += "b";
        break;
    case '-.-.':
        output.value += "c";
        break;
    case '-..':
        output.value += "d";
        break;
    case '.':
        output.value += "e";
        break;
    case '..-.':
        output.value += "f";
        break;
    case '--.':
        output.value += "g";
        break;
    case '....':
        output.value += "h";
        break;
    case '..':
        output.value += "i";
        break;
    case '.---':
        output.value += "j";
        break;
    case '-.-':
        output.value += "k";
        break;
    case '.-..':
        output.value += "l";
        break;
    case '--':
        output.value += "m";
        break;
    case '-.':
        output.value += "n";
        break;
    case '---':
        output.value += "o";
        break;
    case '.--.':
        output.value += "p";
        break;
    case '--.-':
        output.value += "q";
        break;
    case '.-.':
        output.value += "r";
        break;
    case '...':
        output.value += "s";
        break;
    case '-':
        output.value += "t";
        break;
    case '..-':
        output.value += "u";
        break;
    case '...-':
        output.value += "v";
        break;
    case '.--':
        output.value += "w";
        break;
    case '-..-':
        output.value += "x";
        break;
    case '-.--':
        output.value += "y";
        break;
    case '--..':
        output.value += "z";
        break;
    case '-----':
        output.value += "0";
        break;
    case '.----':
        output.value += "1";
        break;
    case '..---':
        output.value += "2";
        break;
    case '...--':
        output.value += "3";
        break;
    case '....-':
        output.value += "4";
        break;
    case '.....':
        output.value += "5";
        break;
    case '-....':
        output.value += "6";
        break;
    case '--...':
        output.value += "7";
        break;
    case '---..':
        output.value += "8";
        break;
    case '----.':
        output.value += "9";
        break;
    case '.-.-.-':
        output.value += ".";
        break;
    case '--..--':
        output.value += ",";
        break;
    case '..--..':
        output.value += "?";
        break;
    case '-.-.--':
        output.value += "!";
        break;
    case '-..-.':
        output.value += "/";
        break;
    case '-.--.':
        output.value += "(";
        break;
    case '-.--.-':
        output.value += ")";
        break;
    case '---...':
        output.value += ";";
        break;
    case '-.-.-.':
        output.value += ";";
        break;
    case '-...-':
        output.value += "=";
        break;
    case '.-.-.':
        output.value += "+";
        break;
    case '-....-':
        output.value += "-";
        break;
    case '..--.-':
        output.value += "_";
        break;
    default:
        break;
    }
};


/*: NonNeg {Int | (>= v 0)} */ "#define";

//PV: rearranged
var code2Text = function code2Text() /*: () -> Top */
{
    var input = edit1.value;
    var output = edit2, s /*: Str */ = "";
    var len = input.length, comb /*: Str */ = "";
    output.value = "";
    if (len < 4000) {
            for (var i /*: NonNeg */ = 0; i < len; i++) {
                if (input.charAt(i) != '.' && input.charAt(i) != '-' && input.charAt(i) != '+' && input.charAt(i) != ' ') {
                    s = input;
                    edit1.value = "";
                    for (var j /*: NonNeg */ = 0; j <= s.length; j++) {
                        if (s.charAt(j) == '.' || s.charAt(j) == '-' || s.charAt(j) == '+' || s.charAt(j) == ' ') {
                            edit1.value += s.charAt(j);
                        }
                    }
                    alert("This is not a valid Morse Code. It should contain only .-+ and the character \"space\"");
                    code2Text();
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
var writeCode = function(c)  /*: (Str) -> Top */ {
    var output = edit2;
  
    switch (c) {
    case 'a':
        edit2; //rkc: to help heap annotation inference, as above
        output.value += ".- ";
        break;
    case 'b':
        output.value += "-... ";
        break;
    case 'c':
        output.value += "-.-. ";
        break;
    case 'd':
        output.value += "-.. ";
        break;
    case 'e':
        output.value += ". ";
        break;
    case 'f':
        output.value += "..-. ";
        break;
    case 'g':
        output.value += "--. ";
        break;
    case 'h':
        output.value += ".... ";
        break;
    case 'i':
        output.value += ".. ";
        break;
    case 'j':
        output.value += ".--- ";
        break;
    case 'k':
        output.value += "-.- ";
        break;
    case 'l':
        output.value += ".-.. ";
        break;
    case 'm':
        output.value += "-- ";
        break;
    case 'n':
        output.value += "-. ";
        break;
    case 'o':
        output.value += "--- ";
        break;
    case 'p':
        output.value += ".--. ";
        break;
    case 'q':
        output.value += "--.- ";
        break;
    case 'r':
        output.value += ".-. ";
        break;
    case 's':
        output.value += "... ";
        break;
    case 't':
        output.value += "- ";
        break;
    case 'u':
        output.value += "..- ";
        break;
    case 'v':
        output.value += "...- ";
        break;
    case 'w':
        output.value += ".-- ";
        break;
    case 'x':
        output.value += "-..- ";
        break;
    case 'y':
        output.value += "-.-- ";
        break;
    case 'z':
        output.value += "--.. ";
        break;
    case '0':
        output.value += "----- ";
        break;
    case '1':
        output.value += ".---- ";
        break;
    case '2':
        output.value += "..--- ";
        break;
    case '3':
        output.value += "...-- ";
        break;
    case '4':
        output.value += "....- ";
        break;
    case '5':
        output.value += "..... ";
        break;
    case '6':
        output.value += "-.... ";
        break;
    case '7':
        output.value += "--... ";
        break;
    case '8':
        output.value += "---.. ";
        break;
    case '9':
        output.value += "----. ";
        break;
    case '.':
        output.value += ".-.-.- ";
        break;
    case ',':
        output.value += "--..-- ";
        break;
    case '?':
        output.value += "..--.. ";
        break;
    case '!':
        output.value += "-.-.-- ";
        break;
    case '/':
        output.value += "-..-. ";
        break;
    case '(':
        output.value += "-.--. ";
        break;
    case ')':
        output.value += "-.--.- ";
        break;
    case ':':
        output.value += "---... ";
        break;
    case ';':
        output.value += "-.-.-. ";
        break;
    case '=':
        output.value += "-...- ";
        break;
    case '+':
        output.value += ".-.-. ";
        break;
    case '-':
        output.value += "-....- ";
        break;
    case '_':
        output.value += "..--.- ";
        break;
    case ' ':
        output.value += "+ ";
        break;
    default:
        break;
    }
};



//PV: rearranged this
var text2Code = function() /*: () -> Top */ {
    var possiblecomb = "abcdefghijklmnopqrstuvwxyz0123456789.,?!/():;=+-_";
    var input /*: Str */ = edit1.value.toLowerCase();
    var output = edit2;
    if (input.length > 1000) //max 1000 characters
    {
        output.value = "The text is too large...";
    }
    else {
        output.value = "";
        for (var i /*: NonNeg */ = 0; i < input.length; i++)
        writeCode(input.charAt(i));
    }
};

