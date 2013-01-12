//59x: added 'var'
//6x: onclick changed to funcs, not text
//removed 2 vars not being used
var request = new XMLHttpRequest();


function view_onOpen() /*:  -> Undef */ {
    getRSS();
}

function getRSS() /*:  -> Undef */ {
    pointer.x = 17;
    var url = "http://www.toptenreviews.com/rss/movies.xml";
    request.open('GET', url, true);
    request.onreadystatechange = showRSS;
    request.send(null);
}

function showRSS() /*:  -> Undef */ {


    if (request.readyState == 4) {
        maindiv.removeAllElements();
        var arr = request.responseText.split("<item>");
        var arr_len = arr.length;
        var arr_ctr = 1;
        var pubDate = arr[1].split("<pubDate>")[1];
        pubDate = pubDate.split("</pubDate>")[0];
        var xml = '<listbox height="200"  width="270" x="1" y="1" autoscroll="true" background="#FFFFFF" ';
        xml += 'itemWidth="270" itemHeight="17" itemSelectedColor="#CBDEEE"';
        xml += ' itemOverColor="#DBEEFE" name="displaylist">';

        xml += '<listitem  height="15" width="270">';
        xml += '<label width="270" bold="true">Top Movies Opening this Week (' + pubDate + ')</label>';
        xml += '</listitem>';

        xml += '<listitem  height="15" width="270">';
        xml += '<label width="270" bold="true"> </label>';
        xml += '</listitem>';

        while (arr_ctr < arr_len - 1) {
            var title = arr[arr_ctr].split("<title>")[1];
            title = title.split("</title>")[0];
            var link = arr[arr_ctr].split("<link>")[1];
            link = link.split("</link>")[0];
            var reviews = arr[arr_ctr].split("<reviews>")[1];
            reviews = reviews.split("</reviews>")[0];
            var img = arr[arr_ctr].split("<img>")[1];
            img = img.split("</img>")[0];
            var ttitle = str_fita(title);
            var t_len = str_len(ttitle.length);
            xml += '<listitem  height="20" width="270">';
            xml += '<img ';
            xml += "src=" + "'" + img + "'" + " ";
            xml += "/>";
            xml += '<a href="' + link + '" valign="top" underline="false" color="#595656" x="37" width="270" bold="true" tooltip="' + title + '" >' + ttitle + '</a>';
            xml += '<a href="' + link + '" valign="top" x="' + t_len + '">' + reviews + '</a>';
            xml += '</listitem>';
            arr_ctr++;
        }
        xml += '<listitem  height="20" width="270">';
        xml += '<label height="20" width="270" bold="true"> </label>';
        xml += '</listitem>';
        xml += '<listitem  height="20" width="270">';
        xml += '<a href="http://movies.toptenreviews.com/" color="#000000" underline="false" width="270" bold="true">Top Ten Movies In Theaters </a>';
        xml += '</listitem>';
        xml += '</listbox>';
        maindiv.appendElement(xml);
        play.visible = true;
        play.width = 18;
        play.height = 18;
        play.x = 175;
        play.y = ((arr_len + 2) * 15 + 83);
        play.tooltip = "Top Movies This Week";
        Aplay.enabled = true;
        Aplay.width = 18;
        Aplay.height = 18;
        Aplay.x = 175;
        Aplay.y = ((arr_len + 2) * 15 + 83);
        Aplay.href = "http://movies.toptenreviews.com/";
    }

}

function getRSS2() /*:  -> Undef */ {
    pointer.x = 61;
    var url = "http://www.toptenreviews.com/rss/games.xml";
    request.open('GET', url, true);
    request.onreadystatechange = showRSS2;
    request.send(null);
}

function showRSS2() /*:  -> Undef */ {

    if (request.readyState == 4) {
        maindiv.removeAllElements();
        var arr = request.responseText.split("<item>");
        //alert(arr);
        var arr_len = arr.length;
        var arr_ctr = 1;
        var xml = '<listbox height="200" width="270" x="1" y="1" autoscroll="true" background="#FFFFFF" ';
        xml += ' itemWidth="270" itemHeight="15" itemSelectedColor="#CBDEEE"';
        xml += ' itemOverColor="#DBEEFE" name="displaylist">';

        xml += '<listitem  height="15" width="270">';
        xml += '<label width="270" bold="true">Top Video Games in Stores this Week</label>';
        xml += '</listitem>';

        xml += '<listitem  height="15" width="270">';
        xml += '<label width="270" bold="true"> </label>';
        xml += '</listitem>';

        while (arr_ctr < arr_len) {
            var title = arr[arr_ctr].split("<title>")[1];
            title = title.split("</title>")[0];
            //alert(title);
            var link = arr[arr_ctr].split("<link>")[1];
            link = link.split("</link>")[0];
            var reviews = arr[arr_ctr].split("<reviews>")[1];
            reviews = reviews.split("</reviews>")[0];
            var img = arr[arr_ctr].split("<img>")[1];
            img = img.split("</img>")[0];
            var ttitle = str_fita(title);
            var t_len = str_len(ttitle.length);
            xml += '<listitem  height="15" width="270">';
            xml += '<img ';
            xml += "src=" + "'" + img + "'" + " ";
            xml += "/>";
            xml += '<a href="' + link + '" valign="top" underline="false" color="#595656" x="37" width="270" bold="true" tooltip="' + title + '" >' + ttitle + '</a>';
            xml += '<a href="' + link + '" valign="top" x="' + t_len + '">' + reviews + '</a>';
            xml += '</listitem>';
            arr_ctr++;
        }

        xml += '</listbox>';

        maindiv.appendElement(xml);
        play.x = 18;
        play.y = 263;
        play.tooltip = "Top Video Games This Week";
        Aplay.x = 18;
        Aplay.y = 263;
        Aplay.href = "http://games.toptenreviews.com/";

    }
}


function getRSS3() /*:  -> Undef */ {
    pointer.x = 134;
    var url = "http://www.toptenreviews.com/rss/software.xml";
    request.open('GET', url, true);
    request.onreadystatechange = showRSS3;
    request.send(null);
}

function showRSS3() /*:  -> Undef */ {

    if (request.readyState == 4) {
        maindiv.removeAllElements();
        var arr = request.responseText.split("<item>");
        var arr_len = arr.length;
        var arr_ctr = 1;
        var xml = '<listbox height="220" width="270" x="1" y="1" autoscroll="true" background="#FFFFFF"';
        xml += ' itemWidth="260" itemHeight="16" itemSelectedColor="#CBDEEE"';
        xml += ' itemOverColor="#DBEEFE" name="displaylist">';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="270" bold="true">Lastest Gold Award Winner Reviews</label>';
        xml += '</listitem>';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="270" bold="true"> </label>';
        xml += '</listitem>';

        while (arr_ctr < arr_len) {
            var title = arr[arr_ctr].split("<title>")[1];
            title = title.split("</title>")[0];
            var link = arr[arr_ctr].split("<link>")[1];
            link = link.split("</link>")[0];
            var ttitle = str_fit(title);
            var num = (ttitle.indexOf("("));
            var ttitle_a = (ttitle.substring(0, num - 1));
            var ttitle_b = (ttitle.substring(num, ttitle.length));
            var x_len = ttitle_a.length * 7;
            xml += '<listitem height="20" width="270">';
            xml += '<a href="' + link + '" valign="top" height="20" underline="true" bold="true">' + ttitle_a + '</a>';
            xml += '<a href="' + link + '" valign="middle" x="' + x_len + '" underline="false" color="#595656"  bold="true">' + ttitle_b + '</a>';
            xml += '</listitem>';
            arr_ctr++;
        }
        xml += '</listbox>';
        maindiv.appendElement(xml);
        play.x = 18;
        play.y = 273;
        play.tooltip = "Top Rated Software";
        Aplay.x = 18;
        Aplay.y = 273;
        Aplay.href = "http://software.toptenreviews.com/";
    }
}

function getRSS4() /*:  -> Undef */ {
    pointer.x = 233;
    var url = "http://www.toptenreviews.com/rss/ce.xml";
    request.open('GET', url, true);
    request.onreadystatechange = showRSS4;
    request.send(null);
}

function showRSS4() /*:  -> Undef */ {

    if (request.readyState == 4) {
        maindiv.removeAllElements();
        var arr = request.responseText.split("<item>");
        var arr_len = arr.length;
        var arr_ctr = 1;
        var xml = '<listbox height="200" width="270" x="1" y="1" autoscroll="true" background="#FFFFFF" ';
        xml += ' itemWidth="270" itemHeight="15" itemSelectedColor="#CBDEEE"';
        xml += ' itemOverColor="#DBEEFE" name="displaylist">';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="270" bold="true">Lastest Reviews</label>';
        xml += '</listitem>';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="270" bold="true"> </label>';
        xml += '</listitem>';

        while (arr_ctr < arr_len) {
            var title = arr[arr_ctr].split("<title>")[1];
            title = title.split("</title>")[0];
            var link = arr[arr_ctr].split("<link>")[1];
            link = link.split("</link>")[0];
            var img = arr[arr_ctr].split("<img>")[1];
            img = img.split("</img>")[0];
            xml += '<listitem  height="20" width="270">';
            xml += '<img ';
            xml += "src=" + "'" + img + "'" + " ";
            xml += "/>";
            xml += '<a href="' + link + '" valign="top" underline="false" color="#595656" x="37" width="270" bold="true" wordwrap="true"  >' + title + '</a>';
            xml += '</listitem>';
            arr_ctr++;
        }
        xml += '</listbox>';
        maindiv.appendElement(xml);
        play.x = 18;
        play.y = 263;
        play.tooltip = "Top Electronics This Week";
        Aplay.x = 18;
        Aplay.y = 263;
        Aplay.href = "http://electronics.toptenreviews.com/";
    }
}

function getRSS5() /*:  -> Undef */ {
    pointer.x = 20;
    var url = "http://www.toptenreviews.com/rss/articles.xml";
    request.open('GET', url, true);
    request.onreadystatechange = showRSS5;
    request.send(null);
}

function showRSS5() /*:  -> Undef */ {

    if (request.readyState == 4) {
        maindiv.removeAllElements();
        var arr = request.responseText.split("<item>");
        var arr_len = arr.length;
        var arr_ctr = 1;
        var xml = '<listbox height="200" width="270" x="1" y="1" autoscroll="true" background="#FFFFFF"';
        xml += ' itemWidth="270" itemHeight="15" itemSelectedColor="#CBDEEE"';
        xml += ' itemOverColor="#DBEEFE" name="displaylist">';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="260" bold="true">Lastest Articles</label>';
        xml += '</listitem>';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="260" bold="true"> </label>';
        xml += '</listitem>';

        while (arr_ctr < arr_len) {
            var title = arr[arr_ctr].split("<title>")[1];
            title = title.split("</title>")[0];
            var link = arr[arr_ctr].split("<link>")[1];
            link = link.split("</link>")[0];
            var ttitle = str_fit(title);
            xml += '<listitem height="20" width="270" >';
            xml += '<a href="' + link + '" valign="top" height="20" width="270" underline="false" color="#595656"  bold="true" tooltip="' + title + '">' + ttitle + '</a>';
            xml += '</listitem>';
            arr_ctr++;
        }
        xml += '</listbox>';
        maindiv.appendElement(xml);
        play.x = 18;
        play.y = 263;
        play.tooltip = "Newest Articles";
        Aplay.x = 18;
        Aplay.y = 263;
        Aplay.href = "http://www.toptenreviews.com/";

    }
}

function getRSS6() /*:  -> Undef */ {
    pointer.x = 60;
    var url = "http://www.toptenreviews.com/rss/blog.xml";
    request.open('GET', url, true);
    request.onreadystatechange = showRSS6;
    request.send(null);
}

function showRSS6() /*:  -> Undef */ {

    if (request.readyState == 4) {
        maindiv.removeAllElements();
        var arr = request.responseText.split("<item>");

        var arr_len = arr.length;
        var arr_ctr = 1;
        var xml = '<listbox height="200" width="270" x="1" y="1" autoscroll="true" background="#FFFFFF"';
        xml += ' itemWidth="270" itemHeight="15" itemSelectedColor="#CBDEEE"';
        xml += ' itemOverColor="#DBEEFE" name="displaylist">';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="270" bold="true">Lastest Blogs</label>';
        xml += '</listitem>';

        xml += '<listitem  height="20" width="270">';
        xml += '<label width="270" bold="true"> </label>';
        xml += '</listitem>';

        while (arr_ctr < arr_len) {
            var title = arr[arr_ctr].split("<title>")[1];
            title = title.split("</title>")[0];
            var link = arr[arr_ctr].split("<link>")[1];
            link = link.split("</link>")[0];
            var ttitle = str_fit(title);
            xml += '<listitem height="20" width="270">';
            xml += '<a href="' + link + '" valign="top" height="20" width="270" underline="false" color="#595656"  bold="true" tooltip="' + title + '">' + ttitle + '</a>';
            xml += '</listitem>';
            arr_ctr++;
        }
        xml += '</listbox>';
        maindiv.appendElement(xml);
        play.x = 18;
        play.y = 263;
        play.tooltip = "TTR Blogs";
        Aplay.x = 18;
        Aplay.y = 263;
        Aplay.href = "http://blog.toptenreviews.com/";


    }
}

function get_content() /*:  -> Undef */ {
    getRSS5();
    or_review_tab.image = "Greviews.png";
    content_tab.image = "Content.png";
    or_review_tab.overImage = "Greviews.png";
    content_tab.overImage = "Content.png";
    movies_button.image = "Articles.png";
    movies_button.overImage = "Articles.png";
    movies_button.downImage = "blank_orange_bar.png";
    movies_button.width = 51;
    movies_button.onclick = getRSS5;
    games_button.image = "blog_button.png";
    games_button.overImage = "blog_button.png";
    games_button.downImage = "blank_orange_bar.png";
    games_button.width = 40;
    games_button.onclick = getRSS6;
    soft_serv_button.image = "videos.png";
    soft_serv_button.overImage = "videos.png";
    soft_serv_button.downImage = "videos.png";
    soft_serv_button.width = 205;
    soft_serv_button.x = 90;
    soft_serv_button.onclick = function () /*: -> Undef */ {};
    electron_button.enabled = false;
    electron_button.visible = false;
}

function get_review() /*:  -> Undef */ {
    view_onOpen();
    or_review_tab.image = "orange_reviews_tab.png";
    content_tab.image = "grey_content_tab.png";
    or_review_tab.overImage = "orange_reviews_tab.png";
    content_tab.overImage = "grey_content_tab.png";
    movies_button.image = "movies_button.png";
    movies_button.overImage = "movies_button.png";
    movies_button.downImage = "blank_orange_bar.png";
    movies_button.width = 46;
    movies_button.onclick = getRSS;
    games_button.image = "game_button.png";
    games_button.overImage = "game_button.png";
    games_button.downImage = "blank_orange_bar.png";
    games_button.width = 43;
    games_button.onclick = getRSS2;
    soft_serv_button.image = "software_serv.png";
    soft_serv_button.overImage = "software_serv.png";
    soft_serv_button.downImage = "blank_orange_bar.png";
    soft_serv_button.width = 108;
    soft_serv_button.x = 93;
    soft_serv_button.onclick = getRSS3;
    electron_button.enabled = true;
    electron_button.visible = true;
}

function str_len(len) /*: Num -> Num */ {
    if (len > 0 && len < 12) {
        len = (len * 7 + 45);
    }
    else if (len >= 12 && len < 20) {
        len = (len * 7 + 30);
    }
    else if (len >= 20 && len < 30) {
        len = (len * 8 + 20);
    }
    else {
        len = (205);
    }
    return len;
}

function str_fit(ttitle) /*: Str -> Str */ {
    ttitle = ttitle.substring(0, 40);
    if (ttitle.length == 40) {
        ttitle += "...";
    }

    return ttitle;
}

function str_fita(ttitle) /*: Str -> Str */ {
    ttitle = ttitle.substring(0, 27);
    if (ttitle.length == 27) {
        ttitle += "...";
    }

    return ttitle;
}
