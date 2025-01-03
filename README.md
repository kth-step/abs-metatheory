<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# ABS Metatheory

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/kth-step/abs-metatheory/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/kth-step/abs-metatheory/actions/workflows/docker-action.yml




Formal metatheory in Coq for the ABS language.

## Meta

- Author(s):
  - Åsmund Kløvstad
  - Karl Palmskog
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.18 or later
- Additional dependencies:
  - [Ott Coq library](https://github.com/ott-lang/ott) 0.33 or later
  - [Equations Coq library](https://github.com/mattam82/Coq-Equations) 1.3 or later
  - [Coq-Std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.9.0 or later
- Coq namespace: `ABS`
- Related publication(s):
  - [ABS: A Core Language for Abstract Behavioral Specification](https://link.springer.com/chapter/10.1007/978-3-642-25271-6_8) doi:[10.1007/978-3-642-25271-6_8](https://doi.org/10.1007/978-3-642-25271-6_8)

## Building instructions

To install all dependencies, do:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.20.0 coq-ott coq-equations coq-stdpp
```

To build when dependencies are installed, do:
```shell
git clone https://github.com/kth-step/abs-metatheory.git
cd abs-metatheory
make   # or make -j <number-of-cores-on-your-machine> 
```

To build a pdf documenting the project, ensure that `ott` and
TeX Live (`pdflatex`) are installed, and do:
```shell
make docs/report/main.pdf
```
Note that the source file to edit for this pdf is `docs/report/main.mng`.

## Documentation

- [latest technical report](https://kth-step.github.io/abs-metatheory/docs/report/main.pdf)
- [latest coqdoc documentation](https://kth-step.github.io/abs-metatheory/docs/coqdoc/toc.html)

See also [ABS Tools](https://github.com/abstools/abstools).
