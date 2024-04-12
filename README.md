# Paxos-Isabelle

## Formalization and safety proof using IO automata

A safety proof of Paxos in Isabelle/HOL (works with [Isabelle2022](https://isabelle.in.tum.de/)).

This is an old proof of Paxos that I wrote a few years back.
It is based on a [theory of IO-Automata](https://github.com/nano-o/IO-Automata), which is a submodule of this repository.

First update the submodule, then:
- Build with `isabelle build -d IO-Automata/ -D . Paxos`
- Edit with `isabelle jedit -d IO-Automata/ Paxos.thy`

See [Paxos.thy](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/Paxos-Isabelle/master/browser_info/Paxos.html)

## Ivy-like formalization and proof

See [FO-Paxos.thy](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/Paxos-Isabelle/master/browser_info/FO-Paxos.html)
