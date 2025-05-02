#!/bin/sh
ROOT=bags.agda 
agda2hs \
    -o ./haskell/ \
    ./agda/${ROOT}
