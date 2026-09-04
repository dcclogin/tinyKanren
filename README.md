# tinyKanren

A minimalist revision of the [miniKanren language](https://github.com/webyrd/miniKanren) with no additional features.

The same language is implemented four times, one directory per host. Each
implementation is self-contained: a core file, and an example file that
requires it and doubles as the test suite.

    racket/mk.rkt               Racket
    racket/examples.rkt
    racket/mk-typed.rkt         Typed Racket
    racket/examples-typed.rkt
    haskell/MK.hs               Haskell
    haskell/Examples.hs
    typescript/MK.ts            TypeScript
    typescript/Examples.ts

## Running the tests

    cd racket     && racket examples.rkt
    cd racket     && racket examples-typed.rkt
    cd haskell    && runghc Examples.hs
    cd typescript && node Examples.ts
