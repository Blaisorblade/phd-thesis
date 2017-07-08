# Building this paper

Building this paper now requires lhs2TeX, for better output. You can install it
using `cabal-install` or `stack`, but below I give instructions using `stack`
because they are going to work on your machine exactly like on mine.

If you're used to doing `cabal install lhs2tex`, you can try it, but I can't
give any guarantee on its effects.

Installing it requires, on a virgin Linux/OS X machine (should work on Windows
but might not be as smooth):

1. installing the
   [Haskell stack build tool](http://docs.haskellstack.org/en/stable/install_and_upgrade/).
2. installing lhs2TeX using stack. I tested this with:

```
stack install --resolver lts-5.5 lhs2tex
```

Installing GHC and cabal isn't necessary for this. Stack will automagically
download needed dependencies and just work, avoiding any sort of Cabal hell.

On OS X with Homebrew, installing stack is as easy as:
```
brew info haskell-stack
```
