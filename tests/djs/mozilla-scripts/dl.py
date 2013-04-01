#!/usr/bin/env python

import os, re
import urllib2

# Limit the number of pages per category
limit_pages = 1 

sort_by ='users'
#can also use:
# - "featured"
# - "created"
# - "rarting"



home_url =  "https://addons.mozilla.org/"
us_ff_url = home_url + "en-US/firefox/"



# Get the links for every category
def get_categories():
  response = urllib2.urlopen(us_ff_url)
  html = response.read()
  m0 = re.search(r'<ul id=\"side-categories\">(.*?)<\/ul>', html, re.DOTALL)
  if m0:
    inter_links = m0.group(1)
    for line in inter_links.splitlines():
      m1 = re.search(r'<a href=\"(.*)\">', line)
      if m1:
        cat_url = home_url + m1.group(1)
        yield cat_url


def get_category_name_from_url(url):
  return url.rsplit("/")[-2]

def get_addon_name_from_url(url):
  return url.rsplit("/")[-1]


def get_addon_xpi(url, target_dir):
  response = urllib2.urlopen(url)
  html = response.read()
  m0 = re.search(\
      r'href=\"(https://addons.mozilla.org/firefox/downloads/file/.*)\"',\
      html)
  if m0:
    # only get the first link
    dl_link = m0.group(1)
    name = get_addon_name_from_url(url)
    wget_cmd = "wget \"" + dl_link + "\"" + \
        " -O " + target_dir + "/" +  name + ".xpi " + \
        "2> /dev/null"
    #print(wget_cmd)
    os.system(wget_cmd)



# Look for the total number pages in an html page
def get_page_count(html):
  m0 = re.search(r'Page <a href=.*a> of <a href=.*>(\d*)</a>', html)
  if m0:
    return int(m0.group(1))
  else:
    return 0


# Returns list of addon urls
def get_all_from_single_category_page(url):
  response = urllib2.urlopen(url)
  html = response.read()
  #print(html)
  search_string = r'<a href=\"(\/en-US\/firefox\/addon\/.*)/\?src=cb-dl-' + sort_by + '\">'
  m0 = re.findall(search_string, html)
  for m in m0:
    yield home_url + m


# Arguments:
# - url: the url of the category to scrape
# 
# TODO: limit the number of pages
def get_all_from_category(url):
  cat_name = get_category_name_from_url(url)
  if not os.path.exists(cat_name):
    os.makedirs(cat_name)
  init_list_url = url + "?sort=" + sort_by
  response = urllib2.urlopen(init_list_url)
  html = response.read()

  for i in range(1, min(limit_pages ,get_page_count(html)) + 1):
    print(cat_name + " :: " + str(i))

    addon_url_list = get_all_from_single_category_page(init_list_url + "&page=" + str(i))
    for addon in addon_url_list:
      print("\t" + addon)
      get_addon_xpi(addon, cat_name)


  


def main():
  for cat in get_categories():
    get_all_from_category(cat)


if __name__ == '__main__':
    main()
