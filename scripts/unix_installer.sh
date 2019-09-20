#!/usr/bin/env bash
# Run as root
if [ "$EUID" -ne 0 ]; then 
  echo "Please run as root"
  exit
fi

if [[ "$OSTYPE" == "linux-gnu" ]]; then
  echo "Detected Linux"
  tar -C /opt -zxf waterproof-ubuntu.tar.gz
if [[ "$OSTYPE" == "darwin" ]]; then
  echo "Detected Linux"
  tar -C /opt -zxf waterproof-macos.tar.gz
else
  echo "This operating system is not supported!"
fi