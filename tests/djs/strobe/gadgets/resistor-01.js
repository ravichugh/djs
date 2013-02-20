//PV : include files:
///*: "tests/djs/strobe/__math.dref" */ "#use";

var Math =
{ 
  floor: function(i) /*: (i: Num) -> Int */ {return 0; },
  pow: function(i,j) /*: (i: Int, j: Int) -> Int */ {return 0; }
};

var Number = function(o) /*: (o: Top) -> Num */ {return 0;}; 

// Resistor Gadget.
var resistance /*: Num */ =  1000;

var currentBandIndex /*: {Int|(and (>= v 0) (< v 5))} */ = 0;

//PV: I think this is the developer's intention:
var numberOfColorBands /*: {Int|(or (= v 5) (= v 4))} */ = 4;

var bandNumberValues
  /*: Ref {Arr({Int|(and (>= v 0) (< v 16))})|(and (packed v) (= (len v) 5))} */ =
  [1, 0, 2, 10, 15]; // Brown, Black, Red, Empty, Blank.

var buttonStrs = /*: {Arr(Str)|(and (packed v) (= (len v) 16))} */
  ["0black", "1brown", "2red", "3orange", "4yellow", "5green", "6blue", "7violet",
   "8gray", "9white", "Empty", "Tbrown", "Tred", "Tgold", "Tsilver", "Blank"];


//PV : added these
var firstBand  /*: Ref {image:Str, downImage:Str, overImage:Str} */ = {};
var secondBand /*: Ref {image:Str, downImage:Str, overImage:Str} */ = {};
var thirdBand  /*: Ref {image:Str, downImage:Str, overImage:Str} */ = {};
var fourthBand /*: Ref {image:Str, downImage:Str, overImage:Str} */ = {};
var fifthBand  /*: Ref {image:Str, downImage:Str, overImage:Str} */ = {};

var firstToleranceButton /*: Ref {image:Str, downImage:Str, overImage:Str, tooltip:Str} */ = {};
var secondToleranceButton /*: Ref {image:Str, downImage:Str, overImage:Str} */ = {};


//PV : rearranging
var addCommas = function(inputStr) /*: (Str) -> Str */ {
    var commaAddedValue /*: Str */ = "";
    var lengthRemaining /*: Int */ = inputStr.length;
    var index /*: Int */ = lengthRemaining - 1;
    var digitCount /*: Int */ = 0;

    while (lengthRemaining > 0) {
        if (digitCount == 3) {
            commaAddedValue = "," + commaAddedValue; // stick a comma in.i
            digitCount = 0;
        }
        commaAddedValue = inputStr.charAt(index--) + commaAddedValue;
        digitCount++;
        lengthRemaining--;
    }

    return (commaAddedValue);
};


//PV : adding var def
var ohms = /*: {value:Str} */ { };


//PV : rearranged this
var doCalculateResistance = function() /*: () -> Top */
{

    var currentBandValue /*: Int */ =0;
    var power=0;

    resistance = 0;
    for (var bandIndex /*: {Int | (>= v 0)} */ = 0; bandIndex < numberOfColorBands - 2; bandIndex++) {
        currentBandValue = bandNumberValues[bandIndex];
        if (currentBandValue > 9) {
            resistance = -1; // Undef.
        } else {
            resistance *= 10;
            resistance += Math.floor(Number(currentBandValue));
        }
    }

    power = bandNumberValues[numberOfColorBands - 2];
    if (power > 9) {
        resistance = -1; // Undef.
    } else {
        power = Math.pow(10, power);
        resistance *= power;
    }

    if (resistance < 0) {
        ohms.value = "Undef";
    } else {
        ohms.value = addCommas(resistance.toString());  //PV: changed toStr() to toString()
    }

    return;
};

var view_onOpen = function() /*: () -> Top */ {
    // Initialize the resistor's color bands to match the bandNumberValues array above.

    firstBand.downImage = "stock_images\\Button" + buttonStrs[bandNumberValues[0]] + "Down.PNG";
    firstBand.image = "stock_images\\Button" + buttonStrs[bandNumberValues[0]] + "Normal.PNG";
    firstBand.overImage = "stock_images\\Button" + buttonStrs[bandNumberValues[0]] + "Over.PNG";
 
    secondBand.downImage = "stock_images\\Button" + buttonStrs[bandNumberValues[1]] + "Down.PNG";
    secondBand.image = "stock_images\\Button" + buttonStrs[bandNumberValues[1]] + "Normal.PNG";
    secondBand.overImage = "stock_images\\Button" + buttonStrs[bandNumberValues[1]] + "Over.PNG";

    thirdBand.downImage = "stock_images\\Button" + buttonStrs[bandNumberValues[2]] + "Down.PNG";
    thirdBand.image = "stock_images\\Button" + buttonStrs[bandNumberValues[2]] + "Normal.PNG";
    thirdBand.overImage = "stock_images\\Button" + buttonStrs[bandNumberValues[2]] + "Over.PNG";

    fourthBand.downImage = "stock_images\\Button" + buttonStrs[bandNumberValues[3]] + "Down.PNG";
    fourthBand.image = "stock_images\\Button" + buttonStrs[bandNumberValues[3]] + "Normal.PNG";
    fourthBand.overImage = "stock_images\\Button" + buttonStrs[bandNumberValues[3]] + "Over.PNG";

    fifthBand.downImage = "stock_images\\Button" + buttonStrs[bandNumberValues[4]] + "Down.PNG";
    fifthBand.image = "stock_images\\Button" + buttonStrs[bandNumberValues[4]] + "Normal.PNG";
    fifthBand.overImage = "stock_images\\Button" + buttonStrs[bandNumberValues[4]] + "Over.PNG";

    //// Initialize the resistor value.
    doCalculateResistance();

    return;
};

// Resistor   color   codes   and   Tolerances
// -------------------------------------------
//    Codes	Colors		    Tolerances
//    -----     ------              ----------
//	0	Black
//	1	Brown		 	 1%
//	2	Red		 	 2%
//	3	Orange
//	4	Yellow
//	5	Green
//	6	Blue
//	7	Violet
//	8	Gray
//	9	White
//		Gold		 	 5%
//		Silver		 	10%



//PV: rearranged this
var drawNewColorBand = function(color) /*: ({Int|(and (>= v 0) (< v 16))}) -> Top */ {
    //TODO: PV: replaced the original switch statement with if.
    if (currentBandIndex == 0) {
      firstBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
      firstBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
      firstBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    }
    else if (currentBandIndex == 1) {
      secondBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
      secondBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
      secondBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    }
    else if (currentBandIndex == 2) {
      thirdBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
      thirdBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
      thirdBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    }
    else if (currentBandIndex == 3) {
      fourthBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
      fourthBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
      fourthBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    }

    return;
};

var doBlackButton = function() /*: () -> Top */ {
    drawNewColorBand(0);
    bandNumberValues[currentBandIndex] = 0;
    doCalculateResistance();

    return;
};

var doBrownButton = function() /*: () -> Top */ {
    drawNewColorBand(1);
    bandNumberValues[currentBandIndex] = 1;
    doCalculateResistance();

    return;
};

var doRedButton = function() /*: () -> Top */ {
    drawNewColorBand(2);
    bandNumberValues[currentBandIndex] = 2;
    doCalculateResistance();

    return;
};

var doOrangeButton = function() /*: () -> Top */ {
    drawNewColorBand(3);
    bandNumberValues[currentBandIndex] = 3;
    doCalculateResistance();

    return;
};

var doYellowButton = function() /*: () -> Top */ {
    drawNewColorBand(4);
    bandNumberValues[currentBandIndex] = 4;
    doCalculateResistance();

    return;
};

var doGreenButton = function() /*: () -> Top */{
    drawNewColorBand(5);
    bandNumberValues[currentBandIndex] = 5;
    doCalculateResistance();

    return;
};

var doBlueButton = function() /*: () -> Top */ {
    drawNewColorBand(6);
    bandNumberValues[currentBandIndex] = 6;
    doCalculateResistance();

    return;
};

var doVioletButton = function() /*: () -> Top */ {
    drawNewColorBand(7);
    bandNumberValues[currentBandIndex] = 7;
    doCalculateResistance();

    return;
};

var doGrayButton = function() /*: () -> Top */{
    drawNewColorBand(8);
    bandNumberValues[currentBandIndex] = 8;
    doCalculateResistance();

    return;
};

var doWhiteButton = function() /*: () -> Top */{
    drawNewColorBand(9);
    bandNumberValues[currentBandIndex] = 9;
    doCalculateResistance();

    return;
};

var doEraseButton = function() /*: () -> Top */ {
    drawNewColorBand(10);
    bandNumberValues[currentBandIndex] = 10;
    doCalculateResistance();

    return;
};


var doFirstToleranceButton = function() /*: () -> Top */ {
    if (numberOfColorBands == 4) {
        fourthBand.downImage = firstToleranceButton.image;
        fourthBand.image = firstToleranceButton.image;
        fourthBand.overImage = firstToleranceButton.image;
    } else {
        fifthBand.downImage = firstToleranceButton.image;
        fifthBand.image = firstToleranceButton.image;
        fifthBand.overImage = firstToleranceButton.image;
    }

    return;
};

var doSecondToleranceButton = function() /*: () -> Top */ {
    if (numberOfColorBands == 4) {
        fourthBand.downImage = secondToleranceButton.image;
        fourthBand.image = secondToleranceButton.image;
        fourthBand.overImage = secondToleranceButton.image;
    } else {
        fifthBand.downImage = secondToleranceButton.image;
        fifthBand.image = secondToleranceButton.image;
        fifthBand.overImage = secondToleranceButton.image;
    }

    return;
};

var doNoneButton = function() /*: () -> Top */ {
    if (numberOfColorBands == 4) {
        fourthBand.downImage = "stock_images\\ButtonBlankNormal.PNG";
        fourthBand.image = "stock_images\\ButtonBlankNormal.PNG";
        fourthBand.overImage = "stock_images\\ButtonBlankNormal.PNG";
    } else {
        fifthBand.downImage = "stock_images\\ButtonBlankNormal.PNG";
        fifthBand.image = "stock_images\\ButtonBlankNormal.PNG";
        fifthBand.overImage = "stock_images\\ButtonBlankNormal.PNG";
    }

    return;
};

//PV: adding def
var currentColorBandArrow /*: Ref {y:Num} */ = {};

var doFirstBand = function() /*: () -> Top */ {
    // Move the arrow pointer.
    currentColorBandArrow.y = 79;
    currentBandIndex = 0;

    return;
};

var doSecondBand = function() /*: () -> Top */ {
    // Move the arrow pointer.
    currentColorBandArrow.y = 105;
    currentBandIndex = 1;

    return;
};

var doThirdBand = function() /*: () -> Top */ {
    // Move the arrow pointer.
    currentColorBandArrow.y = 131;
    currentBandIndex = 2;

    return;
};

var doFourthBand = function() /*: () -> Top */ {
    // This var does = function not need to do anything for a four band resistor.
    if (numberOfColorBands == 5) {
        // Move the arrow pointer.
        currentColorBandArrow.y = 157;
        currentBandIndex = 3;
    }

    return;
};

var doFifthBand = function() /*: () -> Top */ {
    // This is an "empty" var  = function.  The fifth color band should only be set by the Tolerance buttons.
    return;
};

var doSwitchToFourBandResistor = function() /*: () -> Top */ {
    bandNumberValues[2] = 10;
    thirdBand.downImage = "stock_images\\ButtonEmptyNormal.PNG";
    thirdBand.image = "stock_images\\ButtonEmptyNormal.PNG";
    thirdBand.overImage = "stock_images\\ButtonEmptyNormal.PNG";

    bandNumberValues[3] = 10;
    fourthBand.downImage = "stock_images\\ButtonEmptyNormal.PNG";
    fourthBand.image = "stock_images\\ButtonEmptyNormal.PNG";
    fourthBand.overImage = "stock_images\\ButtonEmptyNormal.PNG";

    bandNumberValues[4] = 15;
    fifthBand.downImage = "stock_images\\ButtonBlankNormal.PNG";
    fifthBand.image = "stock_images\\ButtonBlankNormal.PNG";
    fifthBand.overImage = "stock_images\\ButtonBlankNormal.PNG";

    firstToleranceButton.downImage = "stock_images\\ButtonTbrownDown.PNG";
    firstToleranceButton.image = "stock_images\\ButtonTbrownNormal.PNG";
    firstToleranceButton.overImage = "stock_images\\ButtonTbrownOver.PNG";

    secondToleranceButton.downImage = "stock_images\\ButtonTredDown.PNG";
    secondToleranceButton.image = "stock_images\\ButtonTredNormal.PNG";
    secondToleranceButton.overImage = "stock_images\\ButtonTredOver.PNG";

    return;
};

var doSwitchToFiveBandResistor = function() /*: () -> Top */  {
    bandNumberValues[3] = 10;
    fourthBand.downImage = "stock_images\\ButtonEmptyNormal.PNG";
    fourthBand.image = "stock_images\\ButtonEmptyNormal.PNG";
    fourthBand.overImage = "stock_images\\ButtonEmptyNormal.PNG";

    bandNumberValues[4] = 10;
    fifthBand.downImage = "stock_images\\ButtonEmptyNormal.PNG";
    fifthBand.image = "stock_images\\ButtonEmptyNormal.PNG";
    fifthBand.overImage = "stock_images\\ButtonEmptyNormal.PNG";

    firstToleranceButton.downImage = "stock_images\\ButtonTgoldDown.PNG";
    firstToleranceButton.image = "stock_images\\ButtonTgoldNormal.PNG";
    firstToleranceButton.overImage = "stock_images\\ButtonTgoldOver.PNG";

    secondToleranceButton.downImage = "stock_images\\ButtonTsilverDown.PNG";
    secondToleranceButton.image = "stock_images\\ButtonTsilverNormal.PNG";
    secondToleranceButton.overImage = "stock_images\\ButtonTsilverOver.PNG";

    return;
};

//PV: added this def
var numberOfBandsButton /*: Ref Dict */ = {};
var noneButton /*: Ref Dict */ = {};

var toggleNumberOfBandsButton = function() /*: () -> Top */ {
    if (numberOfColorBands == 4) {
        numberOfColorBands = 5;
        numberOfBandsButton.downImage = "stock_images\\Button5Down.PNG";
        numberOfBandsButton.image = "stock_images\\Button5Normal.PNG";
        numberOfBandsButton.overImage = "stock_images\\Button5Over.PNG";
        fourthBand.tooltip = "Resistor's fourth color band";
        fifthBand.tooltip = "Resistor's tolerance band";
        firstToleranceButton.tooltip = "5% Gold will become the fifth band (Tolerance)";
        secondToleranceButton.tooltip = "10% Silver will become the fifth band (Tolerance)";
        noneButton.tooltip = "Remove the fifth band (Tolerance)";
        ohms.tooltip = "Enter an Ohmic value between 0 and 999,000,000,000";
        doSwitchToFiveBandResistor();
    } else { // numberOfColorBands == 5.
        numberOfColorBands = 4;
        numberOfBandsButton.downImage = "stock_images\\Button4Down.PNG";
        numberOfBandsButton.image = "stock_images\\Button4Normal.PNG";
        numberOfBandsButton.overImage = "stock_images\\Button4Over.PNG";
        fourthBand.tooltip = "Resistor's tolerance band";
        fifthBand.tooltip = "";
        firstToleranceButton.tooltip = "1% Brown will become the fourth band (Tolerance)";
        secondToleranceButton.tooltip = "1% Red will become the fourth band (Tolerance)";
        noneButton.tooltip = "Remove the fourth band (Tolerance)";
        ohms.tooltip = "Enter an Ohmic value between 0 and 99,000,000,000";
        doSwitchToFourBandResistor();
    }

    doFirstBand();

    doCalculateResistance();

    return;
};



var containsNonDigit = function(inputStr) /*: (Str) -> Bool */ {
    var stringLength = inputStr.length;
    for (var i /*: { Int | (>= v 0)} */ = 0; i < stringLength; i++) {
        if ((inputStr.charAt(i) < "0") || (inputStr.charAt(i) > "9")) {
            return (true);
        }        
    }

    return (false);
};

var containsLeadingZero = function(inputStr) /*: (Str) -> Bool */ {
    if ((inputStr.charAt(0) == "0") && (inputStr.length != 1)) {
        return (true);
    }

    return (false);
};

var containsErroneousNonZeroDigits = function(inputStr, zerosStartAtPosition)  
/*: (Str, {Int | (>= v 0)}) -> Bool */ {
    var length = inputStr.length;

    if (length <= zerosStartAtPosition) {
        return (false);
    }

    for (var i /*: {Int|(>= v 0)} */ = zerosStartAtPosition; i < length; i++) {
        if (inputStr.charAt(i) != "0") {
            return (true);
        }
    }

    return (false);
};

var removeCommas = function(inputStr) /*: (Str) -> Str */ {
    var noCommasValue /*: Str */ = "";
    var index = 0;

    for (var i /*: {Int|(>= v 0)} */ = 0; i < inputStr.length; i++) {
        if (inputStr.charAt(i) != ",") {
            noCommasValue = noCommasValue + inputStr.charAt(i);
        }
    }

    return (noCommasValue);
};


//PV: added this
var parseNum = /*: (Str) -> Int */ "#extern";

var doGenerateBandColors = function() /*: () -> Top */ {
    var digitStr = resistance.toString();     //PV: changed toStr to toString
    var length = digitStr.length;
    var digit /*: {Int|(and (>= v 0) (< v 16))} */ = 0;

    if (resistance < 0) { // Do NOT update the Color Bands if resistance is UNDEFINED.
        return;
    }

    if (numberOfColorBands == 4) { // Do the first three bands of color bars.
        if (resistance < 10) { // Force the first band color to black.
            firstBand.downImage = "stock_images\\Button0blackDown.PNG";
            firstBand.image = "stock_images\\Button0blackNormal.PNG";
            firstBand.overImage = "stock_images\\Button0blackOver.PNG";
            bandNumberValues[0] = 0;
        } else { // if(resistance >= 10)
            // Process the first digit.
            digit = parseNum(digitStr.charAt(0));
            assume (0 <= digit && digit < 9); //rkc
            firstBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            firstBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            firstBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[0] = digit;
        }

        if (resistance < 10) { // Process the first digit.
            if (length == 0) {
                digit = 0;
            } else {
                digit = parseNum(digitStr.charAt(0));
                assume (0 <= digit && digit < 9); //rkc
            }
            secondBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            secondBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            secondBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[1] = digit;
        } else { // Process the second digit.
            digit = parseNum(digitStr.charAt(1));
            assume (0 <= digit && digit < 9); //rkc
            secondBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            secondBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            secondBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[1] = digit;
        }

        // Process the multiplier.
        if (resistance < 100) {
            thirdBand.downImage = "stock_images\\Button0blackDown.PNG";
            thirdBand.image = "stock_images\\Button0blackNormal.PNG";
            thirdBand.overImage = "stock_images\\Button0blackOver.PNG";
            bandNumberValues[2] = 0;
        } else {
            digit = (digitStr.length - 2);
            assume (0 <= digit && digit < 9); //rkc
            thirdBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            thirdBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            thirdBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[2] = digit;
        }
    } else { // if(numberOfColorBands == 5) { // Do the first four bands of color bars.
        if (resistance < 100) { // Force the first band color to black.
            firstBand.downImage = "stock_images\\Button0blackDown.PNG";
            firstBand.image = "stock_images\\Button0blackNormal.PNG";
            firstBand.overImage = "stock_images\\Button0blackOver.PNG";
            bandNumberValues[0] = 0;
            if (resistance < 10) {
                secondBand.downImage = "stock_images\\Button0blackDown.PNG";
                secondBand.image = "stock_images\\Button0blackNormal.PNG";
                secondBand.overImage = "stock_images\\Button0blackOver.PNG";
                bandNumberValues[1] = 0;
                digit = parseNum(digitStr.charAt(0));
                assume (0 <= digit && digit < 9); //rkc
                thirdBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
                thirdBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
                thirdBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
                bandNumberValues[2] = digit;
            } else { // Resistance is between 10 and 99.
                // Process the first digit.
                digit = parseNum(digitStr.charAt(0));
                assume (0 <= digit && digit < 9); //rkc
                secondBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
                secondBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
                secondBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
                bandNumberValues[1] = digit;
                // Process the second digit.
                digit = parseNum(digitStr.charAt(1));
                assume (0 <= digit && digit < 9); //rkc
                thirdBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
                thirdBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
                thirdBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
                bandNumberValues[2] = digit;
            }
        } else { // if(resistance >= 100)
            // Process the first digit.
            digit = parseNum(digitStr.charAt(0));
            assume (0 <= digit && digit < 9); //rkc
            firstBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            firstBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            firstBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[0] = digit;
            // Process the second digit.
            digit = parseNum(digitStr.charAt(1));
            assume (0 <= digit && digit < 9); //rkc
            secondBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            secondBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            secondBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[1] = digit;
            // Process the third digit.
            digit = parseNum(digitStr.charAt(2));
            assume (0 <= digit && digit < 9); //rkc
            thirdBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            thirdBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            thirdBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[2] = digit;
        }

        // Process the multiplier.
        if (resistance < 1000) {
            fourthBand.downImage = "stock_images\\Button0blackDown.PNG";
            fourthBand.image = "stock_images\\Button0blackNormal.PNG";
            fourthBand.overImage = "stock_images\\Button0blackOver.PNG";
            bandNumberValues[3] = 0;
        } else {
            digit = (digitStr.length - 3);
            assume (0 <= digit && digit < 9); //rkc
            fourthBand.downImage = "stock_images\\Button" + buttonStrs[digit] + "Down.PNG";
            fourthBand.image = "stock_images\\Button" + buttonStrs[digit] + "Normal.PNG";
            fourthBand.overImage = "stock_images\\Button" + buttonStrs[digit] + "Over.PNG";
            bandNumberValues[3] = digit;
        }
    }

    return;
};


//PV: added this - remove it later
var stringToNum = /*: (Str) -> Num */ "#extern";


var doOhmsCheck = function() /*: () -> Top */ {
    var cleanedOhms = removeCommas(ohms.value);    
    var minimumOhmsValue = 0, maximumOhmsValue = 0.0;
    if (numberOfColorBands == 4) {
        minimumOhmsValue = 0;
        maximumOhmsValue = 99000000000.0;
    } else {
        minimumOhmsValue = 0;
        maximumOhmsValue = 999000000000.0;
    }

    //rkc: added explicit stringToNum casts
    if ((stringToNum(cleanedOhms) < minimumOhmsValue)
          || (stringToNum(cleanedOhms) > maximumOhmsValue)
          || (containsNonDigit(cleanedOhms))
          || (containsLeadingZero(cleanedOhms))
          || (containsErroneousNonZeroDigits(cleanedOhms, numberOfColorBands - 2))) {
        ohms.color = "#FF0000"; // Red.
        ohms.strikeout = true;
    } else {
        ohms.color = "#000000"; // Black.
        ohms.strikeout = false;
        resistance = parseNum(cleanedOhms);
    }

    doGenerateBandColors();

    return;
};

