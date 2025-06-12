#!/bin/sh
ROOT=bags.agda 
agda2hs \
    --config agda2hs-rewrites.yaml \
    -o ./haskell/ \
    ./agda/${ROOT} \
    && find ./haskell/ -type f -name '*.hs' -exec cabal run agda2hs-fixer -- {} + \
