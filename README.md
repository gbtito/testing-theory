# Testing-theory
This repository contains the proof methods for testing preorders 
à la [De Nicola](https://dblp.org/pid/n/RDNicola.html) 
and [Hennessy](https://en.wikipedia.org/wiki/Matthew_Hennessy) 
for first-order programs that interact asynchronously,
i.e. via a shared communication medium.

The work is lead by [Giovanni Bernardi](https://www.irif.fr/~gio/).

At present the documentation of the Rocq code 
are Appendix J and Appendix K of this ESOP 2025
[paper](https://hal.science/hal-04642776) penned with
[Ilaria Castellani](https://www-sop.inria.fr/members/Ilaria.Castellani/),
[Paul Laforgue](https://fr.linkedin.com/in/paul-laforgue-16bb48114),
and [Léo Stefanesco](https://stefanesco.com/).

Our Rocq results are currently being developed by [Gaëtan Lopez](https://www.irif.fr/users/glopez/index),
who is supported by a [QuantEDU](https://quantique.france2030.gouv.fr/talents/programme-de-formation/)
scholarship, and is supervised jointly with [Hugo Férée](https://hugo.feree.fr/).


### News

28/10/2026: 
[Roberto Amadio](https://www.irif.fr/users/amadio/index) and I co-authored 
a book on [Operational Methods in Semantics](https://www.worldscientific.com/worldscibooks/10.1142/14882),
which revises and expands Roberto's lecture notes.
Chapter 26 outlines the classical proof techniques for testing preorders, 
and for the must-preorder it tests by Roberto that somewhat differ
from the standard ones.
Chapter 31 presents a new theory of may-preorder for concurrent objects.

28/10/2026: [Maryline Zhang](https://www.irif.fr/users/mzhang/index), [Pedro Ribeiro](https://www.cs.york.ac.uk/people/?username=pfr),
and I co-authored an EXPRESS/SOS 2026 paper that shows how the
maximal-progress axiom breaks standard proof techniques of testing preorders.
The pre-print is available [here](https://expresssos.github.io/assets/pdf/paper_5.pdf). 

28/10/2026: The TOPLAS paper presenting the first constructive characterisation
of the must-preorder for asynchronous systems is now available [here](https://dl.acm.org/doi/10.1145/3842749).

30/11/2025: [Vincent Padovani](https://www.irif.fr/~padovani/) helped writing a journal version of the ESOP paper
that contains two more examples and the entire proof of the main theorem.
The pre-print is available [here](https://www.irif.fr/~gio/submissions/toplas-esop2025.pdf).
