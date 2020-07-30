#!/usr/bin/env python3

import glob
import os
import re
import sys

# DejaGnu's runtest script loads a $(TOOL).exp file from a directory on startup.
# This directory is hardcoded to one of config ../config ../../config or
# ../../../config, so if our testsuite has more than 3 levels of directory
# hierarchy, we need to have have a symlink to config.
# directory. This will catch mistakes if test subdirectories are moved without
# updating CONFDIR to match the change in hierarchy.
conf_re = re.compile(r'^CONFDIR\s*=\s*(.*)$')

exit_code = 0
found_missing = False

fix = len(sys.argv) > 1 and sys.argv[1] == '-fix'

config_paths = ['config', '../config', '../../config', '../../../config']

for makefile in glob.glob('**/Makefile', recursive=True):
    dir_path = os.path.dirname(makefile)
    if not any(os.path.exists(os.path.join(dir_path, c)) for c in config_paths):
        found_missing = True
        if not fix:
            print('Error: {} is missing a symlink to config'.format(dir_path))
            exit_code = 1
        else:
            # Create the symlink as far up the directory tree as possible
            # to minimize the number of symlinks required
            up_3_dirs = os.path.normpath(os.path.join(dir_path, '../../..'))
            dest = os.path.join(up_3_dirs, 'config')

            # The testsuite root config dir relative to the symlink
            src = os.path.relpath('config', up_3_dirs)

            print('Creating symlink {} for {}'.format(dest, dir_path))
            os.symlink(src, dest)

if found_missing and not fix:
    print('Fix with {} -fix'.format(sys.argv[0]))
sys.exit(exit_code)
