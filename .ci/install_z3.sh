#!/bin/bash

set -x

versionShort=4.8.1
version=${versionShort}.016872a5e0f6

if [ ! -f "$HOME/z3/z3-${version}-x64-ubuntu-14.04/bin/z3" ]; then
  mkdir -p $HOME/z3
  if [ "$(ls -A $HOME/z3)" ]; then
      rm -r $HOME/z3/*
  fi
  wget https://github.com/Z3Prover/z3/releases/download/z3-${versionShort}/z3-${version}-x64-ubuntu-14.04.zip -O ~/z3.zip
  unzip ~/z3.zip -d ~/z3
fi

PATH="$HOME/z3/z3-${version}-x64-ubuntu-14.04/bin/:$PATH"
z3 --version
