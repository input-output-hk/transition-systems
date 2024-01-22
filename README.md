Overview
========

The `transition-system` library is an Isabelle framework for working
with labeled transition systems. Its most remarkable feature is an
algebra of “up to” methods for proofs of bisimilarity. The framework is
heavily based on [the technical report *On the Bisimulation Proof
Method* by Davide Sangiorgi][ecs-lfcs-94-299]. However, it goes beyond
what is presented in this report in the following ways:

  * It deals not only with strong but also with weak bisimilarity.
    Repetition is avoided by handling the commonalities of strong and
    weak bisimilarity once, in a sufficiently abstract way.

  * Instead of the “up to context” proof method, it supports “up to
    mutation”, a new proof method that arises as a generalization of “up
    to context” by first going from contexts to arbitrary functions on
    processes and then from these to relations on processes.

  * It uses a point-free style that exerts operations on relations in
    favor of a more low-level style based on predicate logic as much as
    possible. This makes inherent structure much clearer, in particular
    the one that underlies the theory of “up to mutation”.

  * It extends the theory of “up to mutation” to cover also weak
    bisimilarity.

[ecs-lfcs-94-299]:
    https://www.lfcs.inf.ed.ac.uk/reports/94/ECS-LFCS-94-299/
    "On the Bisimulation Proof Method"


Requirements
============

You need Isabelle2022 to use this Isabelle library. You can obtain
Isabelle2022 from the [Isabelle website][isabelle].

[isabelle]:
    https://isabelle.in.tum.de/
    "Isabelle"


Setup
=====

To make this Isabelle library available to your Isabelle installation,
add the path of the `src` directory to the file
`$ISABELLE_HOME_USER/ROOTS`. You can find out the value of
`$ISABELLE_HOME_USER` by running the following command:

    isabelle getenv ISABELLE_HOME_USER


Building
========

Running `make` builds the PDF file that includes the documentation and
the code and places it in `$ISABELLE_BROWSER_INFO/IOG`. You can find out
the value of `$ISABELLE_BROWSER_INFO` by running the following command:

    isabelle getenv ISABELLE_BROWSER_INFO

The makefile specifies two targets: `properly`, which is the default,
and `qnd`. With `properly`, fake proofs (`sorry`) are not accepted; with
`qnd`, quick-and-dirty mode is used and thus fake proofs are accepted.
