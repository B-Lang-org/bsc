#!/usr/bin/env bash
apt-get update

apt-get install -y asciidoctor \
        ruby-asciidoctor-pdf

# ruby-asciidoctor-pdf exists on Ubuntu 20.04 and later
