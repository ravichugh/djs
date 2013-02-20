var power = /*: Num */ "#extern";

var resistance /*: Num */ = 0;

if (power > 9) {
    resistance = -1; // Undef.
} else {
    resistance *= 100;
}

if (resistance < 0) {

} else {
    //rkc: slow if -exactJoins
    assert (typeof resistance.toString() === "string");
}
