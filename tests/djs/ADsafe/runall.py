#! /usr/bin/env python
import re
import time
import string
from multiprocessing import Process, Pipe, Queue
from Queue import Empty
from collections import Counter

from optparse import OptionParser
# filename, timeout for z3

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
                    default="-1",
                    help="give the number of the file to stop at")
parser.add_option(  "-i", "--input",
                    dest="input_file", 
                    default="input.txt",
                    help="give the file that contains the JS sources \
                    (optionally 2nd element will be maximum query time)")
parser.add_option("-t", "--timeout",
                  action="store_true", dest="timeout", default=False,
                  help="enforce the time limits specified in the input file")
parser.add_option("--no-color",
                  action="store_false", dest="color", default=True,
                  help="don't print color messages to stdout")

parser.add_option("-s", "--hackSubArrows",
                  action="store_true", dest="hackSubArrows", default=False,
                  help="don't check arrow subtyping")

parser.add_option("--only-stats",
                  action="store_true", dest="only_stats", default=False,
                  help="only gather statistics about files")

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
    files = list(self.__read_files__())
    a = int(options.file_start) 
    if int(options.file_stop) < 0:
      z = len(files)
    else:
      z = int(options.file_stop)
    self.files = files[a:z]
    print "Running DJS on %d files..." % len(self.files) 
    if options.hackSubArrows:
      print "Using hackSubArrows"
    if options.timeout:
      print "Using timeout"
    print "---------------------------------------------\n"
    
  def __read_files__(self):
    for l in open(options.input_file,"r").readlines():
      ll = l.split()
      if not options.timeout:
        ll = ll[:1] + ["0"]
      if len(ll) == 1:
        ll = ll + ["0"]     # timeout 0 means ignore
      yield ll

  def TC(self):
    def foo((f,t)): 
      s = Source(f,t)
      return (f,s.stats,s.TC())
    return Results(map(foo, self.files))



"""
  Single source file
"""
class Source:

  def __init__(self, f,t):
    self.filename = f
    self.stats = Stats(f)
    self.timeout = t

  def TC(self):
    cmd = Command(self.filename, self.stats, options.hackSubArrows, self.timeout)
    return cmd.execute()


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

  #TODO: clean this up ...
  def __timeit__(self):
    import threading, sys, time, os
    if not self.__done__:
      dt = time.time() - self.__start_time__
      sys.stdout.write("\r%30s :: %s :: ET: %7.2f sec" % (self.input_file,\
        str(self.stats), dt))
      threading.Timer(0.01, self.__timeit__).start()
      sys.stdout.flush()

  def execute(self):
    import subprocess, datetime, os
    cmd = self.__prep__()
    if options.only_stats:
      print("%30s :: %s" % (self.input_file, str(self.stats)))
      return Result()
    else:
      self.__start_time__ = time.time()
      self.__done__ = False
      self.__timeit__()
      self.process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
      stdout = self.process.stdout.read()
      stderr = self.process.stderr.read()
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

  def __init__(self, output=None, time=None):
    self.output       = output
    self.elapsed_time = time
    self.queries      = None
    self.message      = None
    self.success      = False
    if output:
      self.__process__()
    else:
      self.message = ""

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
    if result.elapsed_time:
      self.elapsed_time = self.elapsed_time + result.elapsed_time
    if result.queries:
      self.queries = self.queries + result.queries

  def show(self):
    print "-------------------------------------------------------------"
    if self.elapsed_time:
      print bc.BOLD + "Total       Time : %.2f sec" % self.elapsed_time + bc.ENDC
      print bc.BOLD + "Total    Queries : %d" % self.queries + bc.ENDC
    for s in self.counters:
      print bc.BOLD + "Total %10s : %d" % (s, self.counters[s]) + bc.ENDC


def main():
  p = Project()
  r = p.TC()
  r.show()

if __name__ == '__main__':
  main()
