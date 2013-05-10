#! /usr/bin/env python
import re
import time
import string
from multiprocessing import Process, Pipe, Queue
from Queue import Empty
from collections import Counter

from optparse import OptionParser
# filename, timeout for z3
files = [    
 ("00-adsafe.js", 0),
 ("01-error.js", 0),
 ("02-string_check.js", 0),
 ("03-owns.js", 0),
 ("04-reject_name.js", 0),
 ("05-reject_property.js", 0),
 ("06-reject_global.js", 0),
 ("07-getStyleObject.js", 0),
 ("08-walkTheDOM.js", 0),
 ("09-purge_event_handlers.js", 0),
 ("10-parse_query.js", 1000),
 ("13-quest.js", 0),
 ("14-make_root.js", 0),
 ("15-append.js", 0),
 ("16-blur-check-class.js", 0),
 ("17-clone-empty.js", 0),
 ("18-enable-ephemeral-explode.js", 0),
 ("19-fire.js", 0),
 ("20-focus-fragment.js", 0),
 ("21-get.js", 0),
 ("22-klass-mark-off-on.js", 0),
 ("23-protect.js", 0),
 ("24-replace.js", 0),
 ("25-select.js", 0),
 ("26-style.js", 0),
 ("27-tag-text-title.js", 0),
 ("28-value.js", 0),
 ("29-dom.js", 0),
 ("30-the_event.js", 0),
 ("31-adsafe_create-get.js", 0),
 ("32-adsafe_go.js", 0),
 ("33-adsafe-has-later.js", 0),
 ("34-adsafe-lib-intercept.js", 0)
  ]

"""
  Options
"""
parser = OptionParser(usage='usage: %prog [options] ')

parser.add_option(  "--start",
                    dest="file_start", 
                    default="0",
                    help="give the number of the file to start from")
parser.add_option(  "--stop",
                    dest="file_stop", 
                    default=str(len(files)),
                    help="give the number of the file to stop at")
parser.add_option(  "-t", "--timeout",
                    dest="timeout", 
                    default="0",
                    help="maximum number of seconds to verify")
parser.add_option("--no-color",
                  action="store_false", dest="color", default=True,
                  help="don't print color messages to stdout")

parser.add_option("--hackSubArrows",
                  action="store_true", dest="hackSubArrows", default=False,
                  help="don't check arrow subtyping")

(options, args) = parser.parse_args()


"""
  Colors
"""
class Colors:
  HEADER  = '\033[95m'
  OKBLUE  = '\033[94m'
  OKGREEN = '\033[32m'
  WARNING = '\033[33m'
  FAIL    = '\033[31m'
  BOLD    = '\033[1m'
  ENDC    = '\033[0m'

  def __init__(self):
    if not options.color:
      self.HEADER  = ''
      self.OKBLUE  = ''
      self.OKGREEN = ''
      self.WARNING = ''
      self.FAIL    = ''
      self.ENDC    = ''

bc = Colors()


"""
  Entire project
"""
class Project:

  def __init__(self):
    a = int(options.file_start) 
    z = int(options.file_stop) 
    self.files = files[a:z]
    
  def TC(self):
    #TODO: ignoring time limitation atm
    def foo((f,_)): 
      s = Source(f)
      return (f,s.stats,s.TC())
    return Results(map(foo, self.files))


"""
  Single source file
"""
class Source:

  def __init__(self, f):
    self.filename = f
    self.stats = Stats(f)

  def TC(self):
    cmd = Command(self.filename, self.stats, options.hackSubArrows)
    r = cmd.execute()
    #print("%30s :: %s :: %s" % (self.filename, self.stats, r))
    return r


class Stats:

  _keywords = ["TODO", "XXX", "assume", "PV"]

  def __init__(self, f):
    self.filename = f
    self.st = self.__preprocess__()

  def __preprocess__(self):
    def foo(key):
      count = string.count(open(self.filename).read(), key)
      if count > 0:
        msg = bc.WARNING + "#"+ key + ": %2d" % count + bc.ENDC
      else:
        msg = "#" + key + ": %2d" % count
      return (key,count,msg)
    return map(foo, self._keywords)

  def __iter__(self):
    return iter(self.st)

  def __str__(self):
    def g2(m): return m[2]
    return ", ".join(map(g2,self.st))


"""
  Command class exports:
   - execution of the command
"""
class Command:

  _command   = ["../../../src/system-dref"]
  _std_flags = ["-djs"]

  def __init__(self, input_file, stats, hack_sub_arrows = False, timeout = None):
    self.input_file = input_file
    self.stats = stats
    self.hack_sub_arrows = hack_sub_arrows
    self.timeout = timeout

  def __str__(self):
    return str(args)

  def __prep__(self):
    args = self._command + self._std_flags
    if self.timeout:
      args = args + ["-timeout", str(self.timeout)]
    if self.hack_sub_arrows:
      args = args + ["-hackSubArrows"]
    args = (args + [self.input_file])
    return args
  
  #def timeout_command(command, q):
  #  import subprocess, datetime, os, time, signal
  #  process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  #  q.put(process.stdout.read() + process.stderr.read())    #just append stdout and stderr

  def __timeit__(self):
    import threading, sys, time 
    if not self.__done__:
      threading.Timer(0.01, self.__timeit__).start()
      sys.stdout.write("\r%30s :: %s :: ET: %7.2f sec" % (self.input_file, str(self.stats), time.time() - self.__start_time__))
      sys.stdout.flush()

  def execute(self):
    import subprocess, datetime, os
    cmd = self.__prep__()
    if self.timeout:
      raise NotImplementedError
    else:
      self.__start_time__ = time.time()
      self.__done__ = False
      self.__timeit__()
      process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
      stdout = process.stdout.read()
      stderr = process.stderr.read()
      self.__done__ = True
      duration = float(time.time() - self.__start_time__)
      r = Result(stdout + stderr, duration)
      print(" :: %s" % str(r))
      return r


"""
  Class Result exports:
   - Elapsed time
   - Success status 
   - Message
   - Number of queries (makes sense only if successful)
   - An str() function
"""
class Result:

  _reOK     = re.compile(r'OK! (\d*)')
  _reFail   = re.compile(r'TC ERROR!')
  _rePError = re.compile(r'PARSE ERROR!')
  _reFError = re.compile(r'Fatal error')

  def __init__(self, output, time):
    self.output       = output
    self.elapsed_time = time
    self.queries      = None
    self.message      = None
    self.success      = False
    self.__process__()

  def __str__(self):
    return self.message

  def __process__(self):
    if self.output:
      matchOK = self._reOK.search(self.output)
      if matchOK:
        self.success = True
        self.queries = int(matchOK.group(1))
        self.message = bc.OKGREEN + "OK! %s queries" % self.queries + bc.ENDC
      elif self._reFail.search(self.output):
        self.message = bc.OKGREEN + bc.FAIL + "TC Fail" + bc.ENDC
      elif self._rePError.search(self.output):
        self.message = bc.FAIL + "Parse Error" + bc.ENDC
      elif self._reFError.search(self.output):
        self.message = bc.FAIL + "Fatal Error" + bc.ENDC
      else: 
        self.message = bc.WARNING + "Timed out" + bc.ENDC


"""
  Final results
    Constructor arguments:
     - List that contains tripplets of:
       (filename, stats, result)
"""
class Results:

  def __init__(self, l):
    self.counters     = {}
    self.elapsed_time = 0
    self.queries      = 0
    for (f,s,r) in l:
      self.__update__(s,r)

  def __update__(self, stats, result):
    for (key,count,_) in stats:
      if key in self.counters:
        self.counters[key] = self.counters[key] + count
      else:
        self.counters[key] = count
    self.elapsed_time = self.elapsed_time + result.elapsed_time
    self.queries = self.queries + result.queries

  def show(self):
    print "-------------------------------------------------------------"
    print bc.BOLD + "Total Time    : %.3f sec" % self.elapsed_time + bc.ENDC
    print bc.BOLD + "Total    Queries : %d" % self.queries + bc.ENDC
    for s in self.counters:
      print bc.BOLD + "Total %10s : %d" % (s, self.counters[s]) + bc.ENDC


def main():
  p = Project()
  r = p.TC()
  r.show()

if __name__ == '__main__':
  main()
