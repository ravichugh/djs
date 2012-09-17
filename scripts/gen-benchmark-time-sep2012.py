#!/usr/bin/python
#
# Requires that djs writes the number of Z3 queries in out/num-queries.txt

import os, re, sys, time, math

benchdir = '/tests/djs/oopsla12'
djsdir = os.getenv('DJS_DIR')
latexfile = '/src/out/runningtime-sep2012.tex'

benchmarks = {
  'prototypal': '',
  'pseudoclassical': '',
  'functional': '',
  'parts': '',
  'string-fasta': '',
  'access-binary-trees': '',
  'access-nbody': '',
  'splay': '',
  'typeOf': '',
  'negate': '',
  'counter': '',
  'dispatch': '',
  'passengers': '',
}

def nearestInt(f):
    if f - math.floor(f) < 0.5: i = int(math.floor(f))
    else: i = int(math.ceil(f))
    if i == 0: return 1
    return i

totalQueries = 0
totalTime = 0

oc = open(djsdir + latexfile, 'w+')
for top, _, files in os.walk(djsdir + benchdir):
    for nm in files:       
        bench = re.sub("[.]js", "", nm)
        bench = bench.strip()
        if not bench in benchmarks: raise Exception("unexpected benchmark: " + bench)
        options = benchmarks[bench]
        # LaTeX macros don't like '-' characters, so remove them
        bench = re.sub("-","",bench)
        f = os.path.join(top, nm)
        print bench,
        tBegin = time.time()
        os.system("./system-dref -djs -fast %s %s > /dev/null" % (options, f))
        tDiff = time.time() - tBegin
        numQueriesFile = open(djsdir + '/src/out/num-queries.txt')
        try:
            numQueries = int(numQueriesFile.readline())
        except:
            numQueries = -1
        #iTime = nearestInt(tDiff)
        iTime = tDiff
        if iTime < 0.1:
            iTime = 0.1
        oc.write('\\newcommand{\\benchQueries%s}{%d}\n' % (bench, numQueries))
        oc.write('\\newcommand{\\benchTime%s}{%.1f}\n' % (bench, iTime))
        oc.flush()
        print "%d %.1f" % (numQueries, iTime)
        totalQueries += numQueries
        totalTime += iTime

print "Total Queries : %10d" % totalQueries
#print "Total Time    : %10d" % totalTime
print "Total Time    : %10.1f" % totalTime
