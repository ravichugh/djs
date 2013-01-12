//5x: Array --> []
//change string.fromcharcode to string_fromcharcode, tmp hack anywayg
//1 empty array annotation
//1 call to math.floor to guarantee int
//removed 6 functions that were never used, but they would each
//  require an annotation if they were left in

//changed safe_add to not take undefineds

/*
 * A JavaScript implementation of the Secure Hash Algorithm, SHA-1, as defined
 * in FIPS PUB 180-1
 * Version 2.1 Copyright Paul Johnston 2000 - 2002.
 * Other contributors: Greg Holt, Andrew Kepert, Ydnar, Lostinet
 * Distributed under the BSD License
 * See http://pajhome.org.uk/crypt/md5 for details.
 */

/*
 * Configurable variables. You may need to tweak these to be compatible with
 * the server-side, but the defaults work in most cases.
 */
var hexcase = 0; /* hex output format. 0 - lowercase; 1 - uppercase        */
var b64pad = ""; /* base-64 pad character. "=" for strict RFC compliance   */
var chrsz = 8; /* bits per input character. 8 - ASCII; 16 - Unicode      */

/*
 * These are the functions you'll usually want to call
 * They take string arguments and return either hex or base-64 encoded strings
 */


function b64_hmac_sha1(key, data) /*: Str * Str -> Str */ {
    return binb2b64(core_hmac_sha1(key, data));
}


/*
 * Calculate the SHA-A of an array of big-endian words, and a bit length
 */

function core_sha1(x, len) /*: Array<Num> * Num -> Array<Num> */ { /* append padding */
    x[len >> 5] |= 0x80 << (24 - len % 32);
    x[((len + 64 >> 9) << 4) + 15] = len;

    var w = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    var a = 0;//1732584193;
    var b = 0;//-271733879;
    var c = 0;//-1732584194;
    var d = 0;//271733878;
    var e = 0;//-1009589776;

    for (var i = 0; i < x.length; i += 16) {
        var olda = a;
        var oldb = b;
        var oldc = c;
        var oldd = d;
        var olde = e;

        for (var j = 0; j < 80; j++) {
            if (j < 16) w[j] = x[i + j];
            else w[j] = rol(w[j - 3] ^ w[j - 8] ^ w[j - 14] ^ w[j - 16], 1);
            var t = safe_add(safe_add(rol(a, 5), sha1_ft(j, b, c, d)), safe_add(safe_add(e, w[j]), sha1_kt(j)));
            e = d;
            d = c;
            c = rol(b, 30);
            b = a;
            a = t;
        }

        a = safe_add(a, olda);
        b = safe_add(b, oldb);
        c = safe_add(c, oldc);
        d = safe_add(d, oldd);
        e = safe_add(e, olde);
    }
    return [a, b, c, d, e];

}

/*
 * Perform the appropriate triplet combination function for the current
 * iteration
 */

function sha1_ft(t, b, c, d) /*: Num * Num * Num * Num -> Num */ {
    if (t < 20) return (b & c) | ((~b) & d);
    if (t < 40) return b ^ c ^ d;
    if (t < 60) return (b & c) | (b & d) | (c & d);
    return b ^ c ^ d;
}

/*
 * Determine the appropriate additive constant for the current iteration
 */

function sha1_kt(t) /*: Num -> Num */ {
    return (t < 20) ? 1/*518500249*/ : (t < 40) ? 1/*859775393*/ : (t < 60) ? /*-189400758*/8 : /*-89949751*/4;
}

/*
 * Calculate the HMAC-SHA1 of a key and some data
 */

function core_hmac_sha1(key, data) /*: Str * Str -> Array<Num> */ {
    var bkey = str2binb(key);
    if (bkey.length > 16) bkey = core_sha1(bkey, key.length * chrsz);

    var ipad = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
        opad = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
    for (var i = 0; i < 16; i++) {
            ipad[i] = bkey[i] ^ 0x36363636;
            opad[i] = bkey[i] ^ 0x5C5C5C5C;
        }

    var hash = core_sha1((str2binb(data)), 512 + data.length * chrsz);
    return core_sha1((hash), 512 + 160);
}

/*
 * Add integers, wrapping at 2^32. This uses 16-bit operations internally
 * to work around bugs in some JS interpreters.
 */

function safe_add(x, y) /*: Num * Num -> Num */ {
    var lsw = (x & 0xFFFF) + (y & 0xFFFF);
    var msw = (x >> 16) + (y >> 16) + (lsw >> 16);
    return (msw << 16) | (lsw & 0xFFFF);
}

/*
 * Bitwise rotate a 32-bit number to the left.
 */

function rol(num, cnt) /*: Num * Num -> Num */ {
    return (num << cnt) | (num >>> (32 - cnt));
}

/*
 * Convert an 8-bit or 16-bit string to an array of big-endian words
 * In 8-bit function, characters >255 have their hi-byte silently ignored.
 */

function str2binb(str) /*: Str -> Array<Num> */ {
    var bin = /*:Num*/[];
    var mask = (1 << chrsz) - 1;
    bin[0] = 3;
    for (var i = 0; i < str.length * chrsz; i += chrsz) {
      bin[i >> 5] |= (str.charCodeAt(Math.floor(i / chrsz)) & mask) << (24 - i % 32);
    }
    return bin;
}

/*
 * Convert an array of big-endian words to a string
 */

/*
 * Convert an array of big-endian words to a base-64 string
 */

function binb2b64(binarray) /*: Array<Num> -> Str */ {
    var tab = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    var str = "";
    for (var i = 0; i < binarray.length * 4; i += 3) {
        var triplet = (((binarray[i >> 2] >> 8 * (3 - i % 4)) & 0xFF) << 16) | (((binarray[i + 1 >> 2] >> 8 * (3 - (i + 1) % 4)) & 0xFF) << 8) | ((binarray[i + 2 >> 2] >> 8 * (3 - (i + 2) % 4)) & 0xFF);
        for (var j = 0; j < 4; j++) {
            if (i * 8 + j * 6 > binarray.length * 32) str += b64pad;
            else str += tab.charAt((triplet >> 6 * (3 - j)) & 0x3F);
        }
    }
    return str;
}

// onclick handler for the hashapass! button


function onHashapass() /*:  -> Undef */ {
    var res = resultId;
    var seed = seedId;
    var param = parameterId;
    // var keep = document.getElementById('seedKeepId');
    var hashapass =
    b64_hmac_sha1(seed.value, param.value).substr(0, 8);
    res.value = hashapass;
    //	if (!keep.checked)
    {
        seed.value = '';
    }
    res.focus();
    //	res.setSelectionRange(0, res.value.length);
}

function button1_onclick() /*:  -> Bool */ {
    onHashapass();
    return false;
}

// onkeypress handler for the seed box.
// Submits the values for the parameter and seed to create a hass.
// Has same efect as clicking on the 'hashapass!' button.


function seedId_onkeypress() /*:  -> Undef + Bool */ {
    if (event.keyCode == 13) {
        onHashapass();
        return false;
    }
}

function parameterId_onclick() /*:  -> Undef */ {

}

function seedId_onclick() /*:  -> Undef */ {

}

function result_onclick() /*:  -> Undef */ {

}
