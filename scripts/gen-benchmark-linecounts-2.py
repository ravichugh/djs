#!/usr/bin/python
#
# Running                            ./gen-benchmark-linecounts.py
# produces an intermediate file in   $DJS_DIR/src/out/bench.out
# and a bunch of LaTeX macros in     $DJS_DIR/src/out/linecounts.tex
#
# this version computes Un from un-foo.js and Ann from foo.js
#

import os, re, sys

benchdir = '/tests/apr-benchmarks/v0'
djsdir = os.getenv('DJS_DIR')
outfile = '/src/out/bench.out'
latexfile = '/src/out/linecounts.tex'

benchmarks = ['prototypal', 'pseudoclassical', 'functional', 'parts',
              'string-fasta', 'access-binary-trees', 'access-nbody',
              'splay',
              'typeOf',
              'negate', 'counter', 'dispatch', 'passengers']

os.system('cloc $DJS_DIR/' + benchdir + ' --by-file --skip_uniqueness \
           | grep "^[/]" > ' + djsdir + outfile)
print "Ran CLOC on %s and wrote to %s" % (benchdir,outfile)

totalUn = 0
totalAnn = 0

oc = open(djsdir + latexfile, 'w+')
for line in open(djsdir + outfile):
  line = line.strip()
  tokens = re.split("[ ]*", line)
  if len(tokens) != 4: raise Exception("bad line:\n" + line)
  bench, blank, comments, code = tokens
  m = re.match("^.*/(.*)[.]js$", bench)
  if m:
    bench = m.group(1)
    if bench[0:3] == "un-":
      bench = bench[3:]
      if not bench in benchmarks: raise Exception("unexpected benchmark: " + bench)
      # LaTeX macros don't like '-' characters, so remove them
      bench = re.sub("-","",bench)
      iCode = int(code)
      oc.write('\\newcommand{\\benchUn%s}{%d}\n' % (bench, iCode))
      totalUn += iCode
    else:
      if not bench in benchmarks: raise Exception("unexpected benchmark: " + bench)
      # LaTeX macros don't like '-' characters, so remove them
      bench = re.sub("-","",bench)
      iComments, iCode = int(comments), int(code)
      oc.write('\\newcommand{\\benchAnn%s}{%d}\n' % (bench, iComments + iCode))
      totalAnn += iComments + iCode

print "Processed %s and wrote LaTeX commands to %s" % (outfile, latexfile)

print "Total Un  : %10d" % totalUn
print "Total Ann : %10d" % totalAnn
