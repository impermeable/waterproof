#!/bin/bash

# Compiles the files to make them useable
# during development time.

ALL_FILES=$(find | grep -P '\.v(?!.)')
for v_file in $ALL_FILES
do
    coqc -vos -Q $(pwd) wplib $v_file
done
