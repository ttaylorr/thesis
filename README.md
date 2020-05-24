# Verifying Strong Eventual Consistency in δ-CRDTs

This repository contains artifacts from my undergraduate thesis in verifying
that δ-state CRDTs exhibit strong eventual consistency. It contains the
mechanized proofs for the following two known δ-state CRDTs:

- The δ-GCounter, and

- The δ-GSet

It also contains the source for my thesis, as well as any talks that I have
given about this work.

## Building

To build the thesis, ensure that you have a reasonably modern version of LaTeX
installed, and then run the following:

```ShellSession
$ make
```

If you wish to build the document for the Internet (enabling colorized links and
using consistent left/right margins), you can instead run:

```ShellSession
$ make WEB=1
```

## Advisors

- Dan Grossman

- Talia Ringer

##
