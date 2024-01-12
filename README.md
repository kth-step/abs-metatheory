# ABS Metatheory

Formal metatheory in Coq for the ABS language.

## Meta

- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [Coq Ott library](https://github.com/ott-lang/ott)
- Coq namespace: `ABS`

## Building instructions

To install dependencies, do:

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-ott
```

To build when dependencies are installed, do:

``` shell
git clone https://github.com/kth-step/abs-metatheory.git
cd abs-metatheory
make   # or make -j <number-of-cores-on-your-machine> 
```
