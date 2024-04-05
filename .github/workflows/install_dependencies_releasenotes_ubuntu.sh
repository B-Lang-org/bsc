#!/usr/bin/env bash

apt-get update

apt-get install -y \
  asciidoctor \
  ruby-asciidoctor-pdf

# Update asciidoctor-pdf to the latest version
gem install asciidoctor-pdf
