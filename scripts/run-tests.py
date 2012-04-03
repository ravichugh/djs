#!/usr/bin/python

import sys, re, os

def usage():
    print "Usage: ./run-tests.py (djs|djsLite|functional|imperative)/path <system-d-options>"
    sys.exit()

if len(sys.argv) < 2: # != 2:
    usage()

path = sys.argv[1]
systemdoptions = ' '.join(sys.argv[2:])

if re.match("^djs", path): mode = "-djs"
elif re.match("^djsLite", path): mode = "-djsLite"
elif re.match("^functional", path): mode = ""
elif re.match("^imperative", path): mode = ""
else: usage()

test_dir = os.getenv("DJS_DIR") + "/tests/"

def strip_test_dir(f):
    if re.match("^" + test_dir, f):
        return f[len(test_dir):]
    else:
        return f

def iterate(positive):
    for top, _, files in os.walk(test_dir + path):
        for nm in files:       
            b = re.match("^xx_", nm)
            if positive:
                b = not b
            if b and nm[0] != '.':
                f = os.path.join(top, nm)
                os.system("echo -n '%s  ' && ./system-d %s %s %s | tail -1"
                          % (strip_test_dir(f), mode, systemdoptions, f))

print '\033[91m'
print "***************************************************************"
print "NEGATIVE TESTS"
print '\033[0m'
iterate(False)

print '\033[92m'
print "***************************************************************"
print "POSITIVE TESTS"
print '\033[0m'
iterate(True)

