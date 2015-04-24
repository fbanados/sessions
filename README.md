# sessions
Session Types interpreter implementation.

The main.go is boilerplate code for now waiting for future implementation of the parser.

The expr.y is a goyacc implementation of the original source language.  At this point, is mostly scrap code.

The interesting code of the session program is in escapes.go.
Escapes.go contains an interpreter for a restricted version of the calculus in Capecchi et al. 2014.

The multiparty/ folder contains static code (and tests) for the Session Types paper at POPL 2008 (Honda et al. 2008)

The reduction/ folder contains a conversion from a reduction semantics for a very restricted lambda calculus to an actual interpreter implementation.  Is a must to understand the structure of the interpreter in escapes.go.

