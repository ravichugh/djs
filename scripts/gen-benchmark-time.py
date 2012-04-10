#!/usr/bin/python
#
# Requires that djs writes the number of Z3 queries in out/num-queries.txt

import os, re, sys, time, math

benchdir = '/tests/apr-benchmarks/v1'
djsdir = os.getenv('DJS_DIR')
latexfile = '/src/out/runningtime.tex'

benchmarks = {
  'prototypal': '',
  'pseudoclassical': '',
  'functional': '',
  'parts': '',
  'string-fasta': '',
  'access-binary-trees': '-augmentHeaps -greedyThaws',
  'access-nbody': '-augmentHeaps -greedyThaws',
  'splay': '-augmentHeaps -greedyThaws',
  'typeOf': '-doFalseChecks',
  'negate': '',
  'counter': '-augmentHeaps',
  'dispatch': '',
  'passengers': '-augmentHeaps',
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
        os.system("./system-d -djs -fast %s %s > /dev/null" % (options, f))
        tDiff = time.time() - tBegin
        numQueriesFile = open(djsdir + '/src/out/num-queries.txt')
        try:
            numQueries = int(numQueriesFile.readline())
        except:
            numQueries = -1
        iTime = nearestInt(tDiff)
        oc.write('\\newcommand{\\benchQueries%s}{%d}\n' % (bench, numQueries))
        oc.write('\\newcommand{\\benchTime%s}{%d}\n' % (bench, iTime))
        oc.flush()
        print numQueries, nearestInt(tDiff)
        totalQueries += numQueries
        totalTime += iTime

print "Total Queries : %10d" % totalQueries
print "Total Time    : %10d" % totalTime
