# The Iris tutorial @ POPL'18

For the tutorial material you need to have the following dependencies installed:

- Coq 8.6.1 / 8.7.0 / 8.7.1
- Ssreflect 1.6.4
- Coq-std++ 1.1
- Iris 3.1

*Note:* the tutorial material will not work with earlier versions of Iris, it
is important to install the exact versions as given above.

## Installing Iris via opam

The easiest, and recommend, way of installing Iris and its dependencies is via
the OCaml package manager opam (1.2.2 or newer). You first have to add the Coq
opam repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

Then you can do `opam install coq-iris`.

## Installing Iris from source

If you are unable to use opam, you can also build Iris from source. For this,
make sure to `git checkout` the correct versions, and run `make; make install`
for Ssreflect, Coq-std++ and Iris.

## Compiling the exercises

Run `make` to compile the exercises. You need to have exercise 3 compiled to
work on exercise 4 and 5.

## Documentation

The file `ProofMode.md` in the tutorial material (which can also be found in the
root of the Iris repository) contains a list of the Iris Proof Mode tactics.

If you would like to know more about Iris, we recommend to take a look at:

- http://iris-project.org/tutorial-material.html
  Lecture Notes on Iris: Higher-Order Concurrent Separation Logic
  Lars Birkedal and Aleš Bizjak
  Used for an MSc course on concurrent separation logic at Aarhus University

- https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf
  Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent
  Separation Logic
  Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars
  Birkedal, Derek Dreyer.
  A detailed description of the Iris logic and its model