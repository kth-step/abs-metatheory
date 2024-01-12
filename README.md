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
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [Ott Coq library](https://github.com/ott-lang/ott) 0.33 or later
- Coq namespace: `ABS`
- Related publication(s):
  - [ABS: A Core Language for Abstract Behavioral Specification](https://link.springer.com/chapter/10.1007/978-3-642-25271-6_8) doi:[10.1007/978-3-642-25271-6_8](https://doi.org/10.1007/978-3-642-25271-6_8)

## Building instructions

To install all dependencies, do:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.18.0 coq-ott
```

To build when dependencies are installed, do:

```shell
git clone https://github.com/kth-step/abs-metatheory.git
cd abs-metatheory
make   # or make -j <number-of-cores-on-your-machine> 
```

## Documentation

See also [ABS Tools](https://github.com/abstools/abstools).
