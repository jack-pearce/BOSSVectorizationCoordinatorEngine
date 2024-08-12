#!/bin/bash

# To be run in build directory
# Paths to other repos need to be updated

if [[ $EUID -ne 0 ]]; then
    echo "This script must be run as root (with sudo)."
    exit 1
fi

cp ../Tests/BOSSTests.cpp ./BOSS-prefix/src/BOSS/Tests/

cmake -DCMAKE_BUILD_TYPE=Release -DBOSS_SOURCE_REPOSITORY=/home/jcp122/repos/BOSS -DBOSS_SOURCE_BRANCH=bootstrap_load_partition -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ ..

sudo make