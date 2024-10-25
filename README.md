# 🐪 Dromedary 
> An experimental subset of OCaml, using constraint-based type inference!

[![CircleCI](https://circleci.com/gh/johnyob/dromedary/tree/main.svg?style=svg)](https://circleci.com/gh/johnyob/dromedary/tree/main)
[![Coverage Status](https://coveralls.io/repos/github/johnyob/dromedary/badge.svg?branch=main)](https://coveralls.io/github/johnyob/dromedary?branch=main)

## What is Dromedary?

Dromedary is a work-in-progress implementation of a constraint-based type checker for a large subset of OCaml. It is largely based on the work of François Pottier's [Hindley-Milner elaboration in an applictive style](http://gallium.inria.fr/~fpottier/publis/fpottier-elaboration.pdf) and the constraint language presented in [The Essence of ML Type Inference](http://pauillac.inria.fr/~fpottier/publis/emlti-final.pdf).  

## Features

Dromedary implements *significantly* more features than the language presented in Pottier's [paper](http://gallium.inria.fr/~fpottier/publis/fpottier-elaboration.pdf), including:
- Algebraic data types and pattern matching
- Mutually recursive let bindings
- Side-effecting primitives and the value restriction
- GADTs
- Polymorphic variants
- Semi-explicit first-class polymorphism (record fields only)
- Type abbreviations
- Structures

For a description of the thoery of these extensions in a constraint-based setting, see the [accompanying dissertation](dissertation/main.pdf). 






