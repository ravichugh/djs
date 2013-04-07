#!/usr/bin/env python

import os, re
import urllib2
import glob, zipfile

# File type to unzip
unzip_type = '.xpi'


home_url =  "https://addons.mozilla.org/"
us_ff_url = home_url + "en-US/firefox/"


def unzip_file(archive):
  addon_root = os.path.splitext(archive)[0]
  if not os.path.exists(addon_root):
    os.makedirs(addon_root)
 
  # If the direcrory is not empty ...
  if not os.listdir(addon_root):
    if zipfile.is_zipfile(archive):
      zf = zipfile.ZipFile(archive)
      print("Extracting: " + archive + " ...")
      # Extract to the addon root directory
      try:
        zf.extractall(addon_root)
        open(os.path.join(addon_root,"SUCCESS"), 'w').close()
      except zipfile.BadZipfile:
        open(os.path.join(addon_root,"FAILED_EXTRACTION"), 'w').close()
  else: 
    open(os.path.join(addon_root,"SUCCESS"), 'w').close()
    print("Non-empty root dir: " + addon_root + ". Assuming extracted.")


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
