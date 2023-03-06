# Paxos-Isabelle
A safety proof of Paxos in Isabelle/HOL (works with [Isabelle2022](https://isabelle.in.tum.de/).

This is an old proof of Paxos that I wrote a few years back.
It is based on a [theory of IO-Automata](https://github.com/nano-o/IO-Automata), which is a submodule of this repository.

First update the submodule, then:
- Build with `isabelle build -d IO-Automata/ -D . Paxos`
- Edit with `isabelle jedit -d IO-Automata/ Paxos.thy`
