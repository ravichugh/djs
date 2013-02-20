
var currentBandIndex /*: {Int|(and (>= v 0) (< v 5))} */ = 0;

var buttonStrs =
  ["0black", "1brown", "2red", "3orange", "4yellow", "5green", "6blue", "7violet",
   "8gray", "9white", "Empty", "Tbrown", "Tred", "Tgold", "Tsilver", "Blank"];

var firstBand  /*: Ref Dict */ = {};
var secondBand /*: Ref Dict */ = {};
var thirdBand  /*: Ref Dict */ = {};
var fourthBand /*: Ref Dict */ = {};
var fifthBand  /*: Ref Dict */ = {};

var drawNewColorBand = function(color) /*: ({Int|(and (>= v 0) (< v 16))}) -> Top */ {
    //TODO: PV: replaced the original switch statement with if.
    //switch (currentBandIndex) {
    //case 0:
    //    {
    //        firstBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
    //        firstBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
    //        firstBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    //        break;
    //    }
    //case 1:
    //    {
    //        secondBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
    //        secondBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
    //        secondBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    //        break;
    //    }
    //case 2:
    //    {
    //        thirdBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
    //        thirdBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
    //        thirdBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    //        break;
    //    }
    //case 3:
    //    {
    //        fourthBand.downImage = "stock_images\\Button" + buttonStrs[color] + "Down.PNG";
    //        fourthBand.image = "stock_images\\Button" + buttonStrs[color] + "Normal.PNG";
    //        fourthBand.overImage = "stock_images\\Button" + buttonStrs[color] + "Over.PNG";
    //        break;
    //    }
    //}
    if (currentBandIndex == 0) {
      // rkc: TODO speed up packed array access
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
