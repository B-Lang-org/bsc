#!/usr/bin/env python3

import glob
import os
import re
import sys

# Check that CONFDIR definitions in every Makefile always point at the top level
# directory. This will catch mistakes if test subdirectories are moved without
# updating CONFDIR to match the change in hierarchy.
conf_re = re.compile(r'^CONFDIR\s*=\s*(.*)$')

exit_code = 0

fix = len(sys.argv) > 1 and sys.argv[1] == '-fix'

for makefile in glob.glob('**/Makefile', recursive=True):
    dir_path = os.path.dirname(makefile)
    rel_path = os.path.relpath('.', dir_path)
    expect = '$(realpath {})'.format(rel_path)
    lines = []
    found_broken = False
    for l in open(makefile):
       m = conf_re.match(l.strip())
       if m and m.group(1) != expect:
           exit_code = 1
           print('Error: {} has wrong CONFDIR'.format(makefile))
           print('Expected: CONFDIR = {}'.format(expect))
           print('Found: {}'.format(l.rstrip('\n')))
           if fix:
               print('Fixed.')
           else:
               print('Fix with {} -fix'.format(sys.argv[0]))
           lines.append('CONFDIR = {}\n'.format(expect))
           found_broken = True
       else:
           lines.append(l)
    if found_broken and fix:
        with open(makefile, 'w') as f:
            f.write(''.join(lines))
sys.exit(exit_code)
