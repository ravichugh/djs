#!/usr/bin/env python

import os, re, sys
import urllib2
import glob, zipfile
import sqlite3 as lite

from walk import filter_walk


from optparse import OptionParser



# File type to unzip
archive_ext = '.xpi'
archive_pattern = '*.xpi'
js_ext = '.js'
jsm_ext = '.jsm'


home_url =  "https://addons.mozilla.org/"
us_ff_url = home_url + "en-US/firefox/"



# Option parsing definitions
parser = OptionParser(usage='usage: %prog [options] ')
parser.add_option(  "--db",
                    dest="db_file", default="addons.db",
                    help="give the name of the database file (default is addons.db)")
parser.add_option(  "-d", "--dir",
                    dest="root", default="./",
                    help="give the directory to look for js files (default is ./)")
parser.add_option(  "--depth",
                    dest="depth", default=1,
                    help="give the directory depth to look for extracted .xpi files (default is 1)")
(options, args) = parser.parse_args()


class Database:

  """
  Initialize the database connector object
  """
  def __init__(self,name):
    self.name = name
    self.conn = None
    try:
      #This will create a database if it does not exist
      self.conn = lite.connect(name)
      self.c = self.conn.cursor()
      self.tableMap = {}
    except lite.Error, e:
      print "Error %s:" % e.args[0]
      sys.exit(1)

  """
  Create the table
  """
  def register(self, name, args):
    self.create_table(name, args)
    self.tableMap[name] = args


  """
  Create a table with the given name only if does not exist already. 
  
  Arguments:
    tname: the name of the table to be created  
    args: a list of pairs of names of fields and values
  
  """
  def create_table(self, tname, args):
    sql = 'CREATE TABLE IF NOT EXISTS ' + tname + ' ('
    sql = sql + ', '.join(map(lambda (x,y): x + ' ' + y, args))
    sql = sql + ')'
    #print "Executing sqlite3 command: " + sql
    # Create the table containing fields...
    self.c.execute(sql)
    self.conn.commit()

  
  """
  Insert key value pairs in the table named tname.

  Arguments:
    tname: the name of the table
    vals: tuple of values to be added

  """
  def insert(self, tname, vals):
    keys = self.tableMap[tname]
    #print keys
    #print len(keys)
    #print vals
    sql = 'INSERT INTO ' + tname + ' '\
          'VALUES (' + ', '.join(["?"] * len(keys)) + ');'
    #print sql
    #executemany expects a list of tuples as its second argument
    self.c.execute(sql, vals)
    self.conn.commit()

  """
  Insert key value pairs in the table named tname.

  Arguments:
    tname: the name of the table
    vals: list of tuples of values to be added

  """
  def insertMany(self, tname, lvals):
    keys = self.tableMap[tname]

    sql = 'INSERT INTO ' + tname + ' '\
          'VALUES (' + ', '.join(["?"] * len(keys)) + ');'
    print sql
    #executemany expects a list of tuples as its second argument
    self.c.executemany(sql, map(tuple, lvals))
    self.conn.commit()

  """
  Close the connection to the database
  """
  def close(self):
    if self.conn:
      self.conn.close()
 

"""
Helper functions
"""
def splitpath(path, maxdepth=20):
  ( head, tail ) = os.path.split(path)
  return splitpath(head, maxdepth - 1) + [ tail ] \
      if maxdepth and head and head != path \
      else [ head or tail ]

def get_addon_name_from_url(url):
  return url.rsplit("/")[-1]

# Works for filenames of the form: ./<category>/<name>
def get_name_and_cat(name):
  l = splitpath(name)
  return ("/".join(l[2:]), l[1])
   



class Stats:

  def __init__(self,db):
    self.db = db

  def stats_addon(self,archive):
    # This is the directory of the extracted addon
    addon_root = os.path.splitext(archive)[0]
    if os.path.exists(addon_root):
      js_lines = 0
      for r,d,fs in os.walk(addon_root):
        for f in fs:
          fname = os.path.join(r,f)
          if fname.endswith(js_ext) or fname.endswith(jsm_ext):
            fl = len(open(fname).readlines())
            js_lines = js_lines + fl
            #print("\t" + "%5d" % fl + fname)
      #print(addon_root)
      (n,c) = get_name_and_cat(addon_root)
      print("%6d  %s %s"  % (js_lines,c,n))
      return (c,n,js_lines)


  ## SLOW 
  #def gather_all(self):
  #  for r,d,f in os.walk("./"):
  #    for files in f:
  #      if files.endswith(archive_ext):
  #        yield os.path.join(r,files)

  def gather_all(self):
    print(options.depth)
    for r,d,f,de in filter_walk(options.root, \
        file_pattern=archive_pattern, \
        depth = int(options.depth)):
      for files in f:
        yield os.path.join(r,files)


  # Get stats from all addons
  def stats_all(self): 
    print("Populating store ...")
    fs = self.gather_all()
    return map(self.stats_addon, fs)

  def run(self):
    ts = self.stats_all()    
    self.db.insertMany('addons', ts)


def main():
  db = Database(options.db_file)

  db.register('addons', [('category','TEXT'),('name','TEXT'),('lines','INTEGER')])

  st = Stats(db)
  st.run()


if __name__ == '__main__':
    main()
