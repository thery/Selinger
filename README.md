<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Selinger

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/Selinger/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/Selinger/actions/workflows/docker-action.yml





Formalisation of Selinger's paper :
Remarks on Matsumoto and Amano’s normal form

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [MathComp ssreflect 2.6.0 or later](https://math-comp.github.io)
  - [MathComp algebra 2.6.0 or later](https://math-comp.github.io)
  - [MathComp field 2.6.0 or later](https://math-comp.github.io)
- Rocq/Coq namespace: `Selinger`
- Related publication(s): none

## Building and installation instructions

To build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/thery/Selinger.git
cd Selinger
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



