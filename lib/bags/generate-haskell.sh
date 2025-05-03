#!/bin/sh
ROOT=bags.agda 
agda2hs \
    --config agda2hs-rewrites.yaml \
    -o ./haskell/ \
    ./agda/${ROOT}
