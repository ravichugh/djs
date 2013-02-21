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
 ("10-parse_query.js", 10),
 ("11-hunter.js", 0),
 ("12-pecker.js", 0),
 ("13-quest.js", 0),
 ("14-make_root.js", 0),
 ("15-append.js", 0),
 ("16-blur-check-class.js", 0),
 ("17-clone-empty.js", 0),
 ("18-enable-ephemeral-explode.js", 0),
 ("19-fire.js", 1),
 ("20-focus-fragment.js", 500),
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

(options, args) = parser.parse_args()

timeout = int(options.timeout)


com = ["../../../src/system-dref"]

class bcolors:
  HEADER = '\033[95m'
  OKBLUE = '\033[94m'
  OKGREEN = '\033[32m'
  WARNING = '\033[33m'
  FAIL = '\033[31m'
  ENDC = '\033[0m'

  def disable(self):
    self.HEADER = ''
    self.OKBLUE = ''
    self.OKGREEN = ''
    self.WARNING = ''
    self.FAIL = ''
    self.ENDC = ''




def timeout_command(command, q):
  import subprocess, datetime, os, time, signal
  process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  q.put(process.stdout.read() + process.stderr.read())    #just append stdout and stderr

def command(command):
  import subprocess, datetime, os, time, signal
  process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  return process.stdout.read() + process.stderr.read()

file_range = range(int(options.file_start), int(options.file_stop))

reOK = re.compile(r'OK! (\d*)')
reFail = re.compile(r'TC ERROR!')
rePError = re.compile(r'PARSE ERROR!')
reFError = re.compile(r'Fatal error')
tot_queries = 0
tot_time = 0


def process(fname, output, elapsed_time):
  global tot_queries
  todos = string.count(open(fname).read(), "var")
  if output:
    matchOK = reOK.search(output)
    if matchOK:
      groupOK = matchOK.group
      q = int(groupOK(1))
      tot_queries = tot_queries + q
      print  "%30s (ET: %7.3f sec, #TODOS: %2d) " % (f, elapsed_time, todos) + bcolors.OKGREEN + "OK! %s queries" % q + bcolors.ENDC
    
    matchFail = reFail.search(output)
    if matchFail:
      print "%30s (ET: %7.3f sec, #TODOS: %2d) " % (f, elapsed_time, todos) + bcolors.FAIL + "TC Fail" + bcolors.ENDC

    matchPError = rePError.search(output)
    if matchPError:
      print "%30s (ET: %7.3f sec, #TODOS: %2d) " % (f, elapsed_time, todos) + bcolors.FAIL + "Parse Error" + bcolors.ENDC
    
    matchFError = reFError.search(output)
    if matchFError:
      print "%30s (ET: %7.3f sec, #TODOS: %2d) " % (f, elapsed_time, todos) + bcolors.FAIL + "Fatal Error" + bcolors.ENDC
  else:
    print "%30s (ET: %7.3f sec, #TODOS: %2d) " % (f, elapsed_time, todos) + bcolors.WARNING + "Timed out" + bcolors.ENDC


for i in file_range:
  (f,t) = files[i]
  result_queue = Queue(1)
  if timeout > 0:
    p = Process(target=timeout_command, args=(com + ["-timeout", str(t)] + ["-djs", f], result_queue, ))
    start_time = time.time()
    p.start()
    try:
      output = result_queue.get(True, timeout)
      p.terminate()
      p.join()
    except Empty:
      p.terminate()
      p.join()
      output = None
  else:
    start_time = time.time()
    output = command(com + ["-timeout", str(t)] + ["-djs", f])

  elapsed_time = float(time.time() - start_time)
  tot_time = tot_time + elapsed_time
  process(f, output, elapsed_time)

print "-------------------------------------------------------------"
print  bcolors.OKGREEN + "Total Time: %7.3f sec, Total queries: %d" % (tot_time, tot_queries) + bcolors.ENDC
