default:
    just --list

clean:
    find . -name "*.agdai" -type f -delete

haskell:
    cd lib/bags/ && ./generate-haskell.sh

build:
    cabal build -O -j all

build0:
    cabal build -v0 -O0 -j all

doc target='all':
    cabal haddock -v0 -O0 -j {{target}}

ci:
    just haskell && git diff --exit-code && just build0 && just doc
