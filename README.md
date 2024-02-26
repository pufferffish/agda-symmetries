![agda build status](https://github.com/pufferffish/agda-symmetries/actions/workflows/ci-ubuntu.yml/badge.svg) 
![html build status](https://github.com/pufferffish/agda-symmetries/actions/workflows/ci-html.yml/badge.svg) 

This repository contains the source code, project time log, supervisor meeting minutes, status report,
and dissertation of my individual project for the 4th year of my computing science BSc at the University of Glasgow.

# Abstract

In this project, we study free monoids, free commutative monoids, and their connections with sorting and total
orders. Univalent type theory provides a rigorous framework for implementing these ideas, in the construction
of free algebras using higher inductive types and quotients, and reasoning upto equivalence using categorical
universal properties. The main contributions are a framework for universal algebra (free algebras and their
universal properties), various constructions of free monoids and free commutative monoids (with proofs of their
universal properties), applications to proving combinatorial properties of these constructions, and finally an
axiomatic understanding of sorting. 

# Formalization in Agda

This project is formalized using cubical Agda. A HTML rendered version is hosted [here](https://windtfw.com/agda-symmetries/).

## Prerequisites

This library has been tested with the following software versions:
 * Agda v2.6.4
 * The Cubical library, [version 0.6](https://github.com/agda/cubical/releases/tag/v0.6) (Oct 24, 2023)

## Type checking the code

Type check the code by running Agda:

```console
$ agda index.agda
```

# License

With the exception of the `papers/` directory, all files in this project are
licensed under the terms of the MIT License, see [LICENSE](LICENSE).

All rights reserved for content under the `papers/` directory.
