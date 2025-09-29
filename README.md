---
title: Types for Programs and Proofs
subtitle: DAT350 (Chalmers) / DIT235 (GU)
date: Fall Term 2025 (LP1)
---

<link rel="stylesheet" href="gh-fork-ribbon.css" />
<style>.github-fork-ribbon:before { background-color: #333; }</style>
<a class="github-fork-ribbon" href="https://github.com/teach-types/www" data-ribbon="Sources on GitHub" title="Sources on GitHub">Sources on GitHub</a>

![Agda logo](agda.svg){#id .class width=480}

Most course information is on [Canvas](https://chalmers.instructure.com/courses/35737).

Further course links:
[Schedule on TimeEdit](https://cloud.timeedit.net/chalmers/web/public/riq30Qy6565ZZ5Q59g7650Z56YZ6019X67oY40QQ06o0gQ176qQY.html) /
[Chalmers studieportal](https://www.student.chalmers.se/sp/course?course_id=40833) /
[GU ad (sv)](https://www.gu.se/studera/hitta-utbildning/typer-for-program-och-bevis-dit235) /
[GU kursplan](http://kursplaner.gu.se/pdf/kurs/sv/DIT235) /
[GU course description](http://kursplaner.gu.se/pdf/kurs/en/DIT235) /
[Old course page](https://www.cse.chalmers.se/~coquand/TYPES2.html)

Schedule
========

| Date | Time | Teacher | Title | Reading / Remark |
|-------|----|-|----------------------------|------------------|
| Thu 04/09   | 10-12   | AA | [Introduction to Agda](#lecture-1) | LN 1 - 3; VFP 1, 3; DTW 1, 2.1 - 2.5 |  |
| Mon 08/09   | 13-15   | TC | [Dependent types](#lecture-2) |  |
| _Mon 08/09_ | _15-17_ | AA | [Getting started with Agda](#exercise-1) |  |
| Thu 11/09   | 10-12   | TC | [Proving in Agda](#lecture-3) |  |
| Mon 15/09   | 13-15   | TC | [Introduction to operational semantics and type systems](#lecture-4)  | TPL 1-3 |
| _Mon 15/09_ | _15-17_ | TC | [More on Agda](#exercise-2) | _Homework 1 due_  |
| Thu 18/09   | 10-12   | TC | [Introduction to operational semantics and type systems](#lecture-5)  | TPL 3-4 |
| Mon 22/09   | 13-15   | TC | [Introduction to operational semantics and type systems](#lecture-6)  | TPL 5-10 |
| _Mon 22/09_ | _15-17_ | TC | [More on Agda](#exercise-3) | _Homework 2 due_  |
| Thu 25/09   | 10-12   | TC | [Introduction to operational semantics and type systems](#lecture-7)  |  |
| Mon 29/09   | 13-15   | AA | [More on operational semantics and type systems in Agda](#lecture-8)  |  |
| _Mon 29/09_ | _15-17_ | AA | [More on Agda](#exercise-4) | _Homework 3 due_  |
| Thu 02/10   | 10-12   | AA | [More on operational semantics and type systems in Agda](#lecture-9)  |  |
| Mon 06/10   | 13-15   | AA | [More on operational semantics and type systems in Agda](#lecture-10) |  |
| _Mon 06/10_ | _15-17_ | AA | [Exercises on operational semantics and type systems in Agda](#exercise-5) | _Homework 4 due_  |
| Thu 09/10   | 10-12   | AA | [More on operational semantics and type systems in Agda](#lecture-11) |  |
| Mon 13/10   | 13-15   | TC | Student presentations |   |
| Mon 13/10   | 15-17   | TC | Student presentations |   |
| Thu 16/10   | 10-12   | TC | Student presentations |   |
| Mon 20/10   | 13-15   | TC | Student presentations |   |
| Mon 20/10   | 15-17   | TC | Student presentations |   |
| Tue 21/10   | 08-     |    | Take home exam | _Deadline: Fri 24/10 12:00 (noon)_ |

Teachers: TC = [Thierry Coquand](http://www.cse.chalmers.se/~coquand/), AA = [Andreas Abel](http://www.cse.chalmers.se/~abela/).
Room: Lecture hall [MC](https://maps.chalmers.se/#4746a62f-a989-4e43-8ba1-cc624c0685a2).

Literature
==========

Further literature and online access to books via the library can be found on [Canvas](https://chalmers.instructure.com/courses/35737/assignments/syllabus).

* LN  = [An Introduction to Programming and Proving in Agda](http://www.cse.chalmers.se/~peterd/papers/AgdaLectureNotes2018.pdf) (draft), lecture notes
* DTW = [Dependent Types at Work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)
* VFP = [Verified Functional Programming in Agda](http://dl.acm.org/citation.cfm?id=2841316)
* TPL = [Types and Programming Languages](http://www.cis.upenn.edu/~bcpierce/tapl/index.html)

Lectures
========

## Lecture 1

- Introduction to Agda
- Simply-typed programming in Agda

Agda code: [live code start](live/Lecture1.agda), [solution](src/Lecture1.agda), [rendered](src/html/Lecture1.html)

## Lecture 2

- General introduction to logic and dependent types [slides](slides/lecture2.pdf)
- Example of Turing Machines in Agda, how to formulate non termination

## Exercise 1

Getting started with Agda.
Help-session where Andreas will help you get started with Agda programming.
Before this session you need to install Agda and try to write your first Agda programs.
We'll do some simple exercises in Agda.

## Lecture 3

- More on Turing machines
- Inductive predicates
- Propositional and predicate logic
- Propositions as Types, Natural Deduction in Agda

## Lecture 4

- Data types, induction and indexed data types
- Proof by induction on Data Types
- Indexed Data Types: typed expression
- Equality as an Indexed Data Type
- Definitional Equality versus Equality as Type ("book equality")

## Lecture 5

- Hilbert and Gentzen calculus in Agda for propositional logic with implication
- Show equivalence (deduction theorem)
- Run equivalence as proof transformation
- Untyped arithmetic expressions and operational semantics (small-step and big-step)
- Typed predicate on arithmetic expressions
- Progress and preservation theorems

## Lecture 6

- General results on untyped lambda calculus:
- Confluence of reduction
- Equivalence from reduction
- Representation of untyped lambda calculus in Agda

## Lecture 7

- Correctness of a simple compiler to stack machine with addition
- Krivine machine

## Lecture 8

(Lecture 8 and following)

More on operational semantics and type systems in Agda
- Denotational semantics for typed lambda-calculus
- Normalization for typed lambda-calculus
- Confluence in Agda (Parallel substituion method)
- Machine (KAM) for classical logic (Peirce CC)
- Evidence-producing type-checker

## Lecture 9

TBA

## Lecture 10

TBA

## Lecture 11

TBA


Software
========

We recommend Agda version 2.8.0 (recent older versions are also ok).

Installing Agda from binary
---------------------------

1. Download a suitable binary package from https://github.com/agda/agda/releases/tag/v2.8.0 and put it in your PATH
2. Run `agda --setup`

Installing Agda from source
---------------------------

0. Install latest Haskell (see below)
1. Install Agda from Stackage nightly: `stack install --resolver=nightly Agda`
2. Run `agda --setup`
3. Set up the Agda mode (see below)

Installing Haskell
------------------

1. Install [GHCup](https://www.haskell.org/ghcup/)
2. Install latest Stack (3.7.1) and GHC (9.12.2) from within `ghcup tui`
3. Ensure that the path printed by `stack path --local-bin` is in your system PATH

Setting up the Agda mode (Emacs)
--------------------------------

1. Compile the Emacs lisp files: `agda-mode compile`
2. Install the Agda mode: `agda-mode setup`

Setting up the Agda mode (VSCode)
---------------------------------

Get the `agda-mode` extension (authored by Ting-Gian LUA).
