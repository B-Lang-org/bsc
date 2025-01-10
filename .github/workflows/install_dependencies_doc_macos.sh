#!/usr/bin/env bash

brew update

# The install of 'texlive' may cause the install of a newer version of
# 'python', which could fail because it cannot overwrite links for
# older versions, due to an issue with the GitHub runner images:
#   https://github.com/actions/runner-images/issues/9966
# To avoid that, we unlink and install with overwrite:
#
for python_package in $(brew list | grep python@); do
    brew unlink ${python_package} && brew link --overwrite ${python_package}
done

brew install texlive
