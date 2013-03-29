#!/usr/bin/env python

import os, re
import urllib2
import glob, zipfile

# File type to unzip
unzip_type = '.xpi'


home_url =  "https://addons.mozilla.org/"
us_ff_url = home_url + "en-US/firefox/"


def unzip_file(path):
  addon_root = os.path.splitext(path)[0]
  if not os.path.exists(addon_root):
    os.makedirs(addon_root)
  
  #if zipfile.is_zipfile(path):

  



# Unzip all files with the ending 'unzip_type'
def unzip_all(): 
  for r,d,f in os.walk("./"):
    for files in f:
      if files.endswith(unzip_type):
        unzip_file(os.path.join(r,files))


def main():
  unzip_all()


if __name__ == '__main__':
    main()
