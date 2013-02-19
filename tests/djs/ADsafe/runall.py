#! /usr/bin/env python
import re
import time
from multiprocessing import Process, Pipe, Queue
from Queue import Empty

from optparse import OptionParser

files = [    
  "00-adsafe.js",
  "01-error.js",
  "02-string_check.js",
  "03-owns.js",
  "04-reject_name.js",
  "05-reject_property.js",
  "06-reject_global.js",
  "07-getStyleObject.js",
  "08-walkTheDOM.js",
  "09-purge_event_handlers.js",
  "10-parse_query.js",
  "11-hunter.js",
  "12-pecker.js",
  "13-quest.js",
  "14-make_root.js",
  "15-append.js",
  "16-blur-check-class.js",
  "17-clone-empty.js",
  "18-enable-ephemeral-explode.js",
  "19-fire.js",
  "20-focus-fragment.js",
  "21-get.js",
  "22-klass-mark-off-on.js",
  "23-protect.js",
  "24-replace.js",
  "25-select.js",
  "26-style.js",
  "27-tag-text-title.js",
  "28-value.js",
  "29-dom.js",
  "30-the_event.js",
  "31-adsafe_create-get.js",
  "32-adsafe_go.js",
  "33-adsafe-has-later.js",
  "34-adsafe-lib-intercept.js"
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


com = ["../../../src/system-dref", "-djs"]

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
  q.put(process.stdout.read())

def command(command):
  import subprocess, datetime, os, time, signal
  process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  return process.stdout.read()

file_range = range(int(options.file_start), int(options.file_stop))

reOK = re.compile(r'OK! (\d*)')
reFail = re.compile(r'TC ERROR!')
rePError = re.compile(r'PARSE ERROR!')
tot_queries = 0
tot_time = 0


def process(output, elapsed_time):
  global tot_queries
  if output:
    matchOK = reOK.search(output)
    if matchOK:
      groupOK = matchOK.group
      q = int(groupOK(1))
      tot_queries = tot_queries + q
      print  "%30s (ET: %7.3f sec) " % (f, elapsed_time) + bcolors.OKGREEN + "OK! %s queries" % q + bcolors.ENDC
    
    matchFail = reFail.search(output)
    if matchFail:
      print "%30s (ET: %7.3f sec) " % (f, elapsed_time) + bcolors.FAIL + "TC Fail" + bcolors.ENDC

    matchPError = rePError.search(output)
    if matchPError:
      print "%30s (ET: %7.3f sec) " % (f, elapsed_time) + bcolors.FAIL + "Parse Error" + bcolors.ENDC
  else:
    print "%30s (ET: %7.3f sec) " % (f, elapsed_time) + bcolors.WARNING + "Timed out" + bcolors.ENDC


for i in file_range:
  f = files[i]
  result_queue = Queue(1)
  if timeout > 0:
    p = Process(target=timeout_command, args=(com + [f], result_queue, ))
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
    output = command(com + [f])

  elapsed_time = float(time.time() - start_time)
  tot_time = tot_time + elapsed_time
  process(output, elapsed_time)

print "-------------------------------------------------------------"
print  bcolors.OKGREEN + "Total Time: %7.3f sec, Total queries: %d" % (tot_time, tot_queries) + bcolors.ENDC
