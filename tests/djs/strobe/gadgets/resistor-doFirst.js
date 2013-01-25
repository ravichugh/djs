
var numberOfColorBands /*: {Int|(or (= v 5) (= v 4))} */ = 4;

var fourthBand /*: Ref {} */ = {};
var fifthBand  /*: Ref {} */ = {};

var firstToleranceButton  /*: Ref {image:Str} */ = {};

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
