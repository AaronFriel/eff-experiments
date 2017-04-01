# Graph Monad

This library implements a variety of extensible effects frameworks. The goal is to create a generalized "Graph Monad" that achieves an improvement over the implementation of the "freer monad" `Eff` described in "Extensible Effects", and improved upon in "Freer Monads, Extensible Effects".

Recommended reading to understand the background includes:

* H. Apfelmus. [The Operational monad tutorial](http://apfelmus.nfshost.com/articles/operational-monad.html)
* A. Bauer, M. Pretnar. [Programming with Algebraic Effects and Handlers](https://arxiv.org/pdf/1203.1539.pdf) (2012)
* O. Kammar, S. Lindley, and N. Oury. [Handlers in Action](http://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf) (2012)
* O. Kiselyov, A. Sabry, and C. Swords. [Extensible Effects: an Alternative to Monad Transformers](http://www.cs.indiana.edu/~sabry/papers/exteff.pdf) (2013)
* A. Ploeg and O. Kiselyov. [Reflection without Remorse](http://okmij.org/ftp/Haskell/zseq.pdf) (2014)
* O. Kiselyov and H. Ishii. [Freer Monads, More Extensible Effects](http://okmij.org/ftp/Haskell/extensible/more.pdf) (2015)
* O. Kiselyov. [Parameterized Extensible Effects and Session Types](http://okmij.org/ftp/Haskell/extensible/param-eff.pdf) (2016)