#!/usr/bin/python
#
# Running                            ./gen-benchmark-table.py
# produces an intermediate file in   $DJS_DIR/src/out/bench.out
# and a bunch of LaTeX macros in     $DJS_DIR/src/out/linecounts.tex
#
# TODO DJS files contain assert() and "#define" statements, which get
# counted as code lines. should subtract only lines like this.
#

import os, re, sys

benchdir = '/tests/apr-benchmarks/v0'
djsdir = os.getenv('DJS_DIR')
outfile = '/src/out/bench.out'
latexfile = '/src/out/linecounts.tex'

os.system('cloc $DJS_DIR/' + benchdir + ' --by-file --skip_uniqueness \
           | grep "^[/]" > ' + djsdir + outfile)
print "Ran CLOC on %s and wrote to %s" % (benchdir,outfile)

oc = open(djsdir + latexfile, 'w+')
for line in open(djsdir + outfile):
  line = line.strip()
  tokens = re.split("[ ]*", line)
  if len(tokens) != 4: raise Exception("bad line:\n" + line)
  bench, blank, comments, code = tokens
  m = re.match("^.*/(.*)[.]js$", bench)
  if m:
    bench = m.group(1)
    # LaTeX macros don't like '-' characters, so remove them
    bench = re.sub("-","",bench)
    iComments, iCode = int(comments), int(code)
    oc.write('\\newcommand{\\benchUn%s}{%d}\n' % (bench, iCode))
    oc.write('\\newcommand{\\benchAnn%s}{%d}\n' % (bench, iComments + iCode))
print "Processed %s and wrote LaTeX commands to %s" % (outfile, latexfile)

