# Formalization of Iterative Sets

This repository is part of my master thesis ["The Category of Iterative Sets in Cubical Agda"](https://grubmueller.dev/publications/2026-mt-iterative-sets/). It is a fork of the [`Agda.Cubical` library](https://github.com/agda/cubical). The changes are as follows:

- `Cubical.Data.W`: contribution of the disproof of $x \notin x$
- `Cubical.Data.IterativeMultisets`: formalization of $V^\infty$
- `Cubical.Data.IterativeSets`: formalization of $V^0$
- `Cubical.Categories.Instances.IterativeSets`: implementation of category $\cal{V}$
- `Cubical.Categories.WithFamiliesNaive`: naive approach defining CwF and $\Sigma$-structure and instantiating them for iterative sets. This is mostly following along the previous formalization with some major adaptations in the implementation
- `Cubical.Categories.WithFamiliesCubical`: improvement defining the naturality condition for CwF as a heterogenous path
- `Cubical.Categories.WithFamiliesAdHoc`: improvement using ad-hoc functions instead of transport. This is the most complete formalization so far
- Various minor changes can be found throughout the library, notably in the `Cubical.Functions.Embedding` module.


A standard library for Cubical Agda
===================================

The source code has a glorious clickable [rendered version](https://agda.github.io/cubical/Cubical.Everything.html).

There is also a [discord server](https://discord.gg/yjTKHzepMx), shared with [agda-unimath](https://unimath.github.io/agda-unimath/) and the [1lab](https://1lab.dev/).

Compiling, using and installing
-------------------------------
This library checks with [Agda](https://github.com/agda/agda/) version indicated in the table below.
For detailed install instructions see the
[INSTALL](https://github.com/agda/cubical/blob/master/INSTALL.md)
file.
If you want to use some specific release of Agda,
the following table lists which releases of Agda are known to work with which release of this library.
Most likely, a lot more combinations work as well.
Agda versions as written below, correspond to tags.

| cubical library version | Agda versions                  |
|-------------------------|--------------------------------|
| current master          | `v2.8.0`                       |
| `v0.9`                  | `v2.8.0`                       |
| `v0.8`                  | `v2.6.4.1` `v2.7.0.1`          |
| `v0.7`                  | `v2.6.4` `v2.6.4.1`            |
| `v0.6`                  | `v2.6.4`                       |
| `v0.5`                  | `v2.6.3` `v2.6.4`              |
| `v0.4`                  | `v2.6.2.2`                     |
| `v0.3`                  | `v2.6.2`                       |
| `v0.2`                  | `v2.6.1.3`                     |
| `v0.1`                  | `v2.6.0.1`                     |

For example, if you have Agda 2.6.2.2, you can switch to version 0.4 of the cubical library with
```
git checkout v0.4
```

Learning materials
------------------
* Introductory material from the HoTTest summer school:
  [literate agda files](https://github.com/martinescardo/HoTTEST-Summer-School/tree/main/Agda/Cubical)
  [recordings on youtube](https://www.youtube.com/channel/UC-9jDbJ-HegCFuWuam1SfvQ)

* For an introduction to this library, see this [blog
  post](https://homotopytypetheory.org/2018/12/06/cubical-agda/). Note that many
  files and results have moved since this blog post was written.

* For some introductory lecture notes see the material for the Cubical Agda course
  of the [EPIT 2021 spring school](https://github.com/HoTT/EPIT-2020/blob/main/04-cubical-type-theory/).


Theoretical background
----------------------
For a paper with details about Cubical Agda, see [Cubical Agda: a dependently typed
programming language with univalence and higher inductive
types](https://dl.acm.org/doi/10.1145/3341691) by Andrea Vezzosi, Anders
Mörtberg, and Andreas Abel.

The type theory that Cubical Agda implements is a variation of the
cubical type theory of:

[Cubical Type Theory: a constructive interpretation of the univalence
axiom](https://arxiv.org/abs/1611.02108) - Cyril Cohen, Thierry
Coquand, Simon Huber, Anders Mörtberg.


The key difference is that the Kan composition operations are
decomposed into homogeneous composition and generalized transport as
in:

[On Higher Inductive Types in Cubical Type
Theory](https://arxiv.org/abs/1802.01170) - Thierry Coquand, Simon
Huber, Anders Mörtberg.

This makes it possible to directly represent higher inductive types.


Reviewing of [pull requests](https://github.com/agda/cubical/pulls?q=is%3Apr+is%3Aopen+draft%3Afalse)
--------------------------
If you switch your draft pull request (PR) to 'ready to merge',
or directly create an open PR,
we should request a review, by one of the reviewers below.
If that doesn't happen, you can also request a reviewer yourself (for reviewer expertise see below),
to make us aware of the open PR. Feel free to use Discord to get in touch with a reviewer in case reviewing is taking a very long time.

| Reviewer                                                                | github handle | Area of expertise                           |
|-------------------------------------------------------------------------|---------------|---------------------------------------------|
| [Anders Mörtberg](https://staff.math.su.se/anders.mortberg/)            | [mortberg](https://github.com/mortberg) | *Most topics*  |
| [Evan Cavallo](https://ecavallo.net/)                                   | [ecavallo](https://github.com/ecavallo) | *Most topics*  |
| [Felix Cherubini](https://felix-cherubini.de)                           | [felixwellen](https://github.com/felixwellen) | *Mainly algebra related topics* |
| [Max Zeuner](https://www.su.se/english/profiles/maze1512-1.450461)      | [mzeuner](https://github.com/mzeuner) | *Algebra related topics*                   |
| [Axel Ljungström](https://aljungstrom.github.io)                        | [aljungstrom](https://github.com/aljungstrom) | *Synthetic homotopy theory and cohomology* |
| [Andrea Vezzosi](http://saizan.github.io/)                              | [Saizan](https://github.com/Saizan)   | *Inactive*                                 |

[Overview](https://github.com/agda/cubical/pulls?q=is%3Apr+is%3Aopen+sort%3Aupdated-asc+draft%3Afalse) of the current open PRs, descending time since last action.
