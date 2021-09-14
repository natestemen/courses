# courses

A repo for my coursework as a phd student at the University of Waterloo in the applied math department, with a specialization in quantum information.

So far I've mostly taken courses pretty seriously, but I know grades during a PhD basically don't matter. For that reason I try not to spend crazy amounts of time on homeworks, but if I do, chances are it's because I'm fiddling with LaTeX, not doing homework. I've learned a lot of cool TeX things by doing my homework like drawing quantum circuit diagrams, plotting functions, and doing things with colors.

## Year 1 (2020-2021)

### Fall 2020

| Course                                                                                                                                     | Professor                                                       | Directory                  | PDFs                                                          |
| ------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------- | -------------------------- | ------------------------------------------------------------- |
| Numerical Analysis                                                                                                                         | [Hans De Sterck](http://www.hansdesterck.net/)                  | [`numerical`](./numerical) | [link](https://natestemen.xyz/latex/numerical-analysis/)      |
| [Advanced Quantum Theory](https://uwaterloo.ca/physics-of-information-lab/teaching/advanced-quantum-theory-amath-473673-phys454-fall-2020) | [Achim Kempf](https://uwaterloo.ca/physics-of-information-lab/) | [`qtheory`](.qip)          | [link](https://natestemen.xyz/latex/quantum-theory/)          |
| [Quantum Info. Processing](http://cleve.iqc.uwaterloo.ca/qic710/index.html)                                                                | [Richard Cleve](http://cleve.iqc.uwaterloo.ca/)                 | [`qip`](./qip)             | [link](https://natestemen.xyz/latex/quantum-info-processing/) |

### Winter 2021

| Course                    | Professor                                                                    | Directory      | PDFs                                                       |
| ------------------------- | ---------------------------------------------------------------------------- | -------------- | ---------------------------------------------------------- |
| Open Quantum Systems      | [Joseph Emerson](https://services.iqc.uwaterloo.ca/people/profile/jemerson/) | [`oqs`](./oqs) | [link](https://natestemen.xyz/latex/open-quantum-systems/) |
| Lie Groups & Lie Algebras | [Da Rong Cheng](https://sites.google.com/view/daren-cheng)                   | [`lie`](./lie) | [link](https://natestemen.xyz/latex/lie-theory/)           |

### Summer 2021

| Course                                                                                | Professor                                            | Directory      |
| ------------------------------------------------------------------------------------- | ---------------------------------------------------- | -------------- |
| [Software Verification using Proof Assistants](https://cs.uwaterloo.ca/~plragde/747/) | [Prabhakar Ragde](https://cs.uwaterloo.ca/~plragde/) | [`swv`](./swv) |

## Year 2 (2021-2022)

### Fall 2021

| Course                                                                                                                                   | Professor         | Interest                                                                                                                                                                                                                                  |
| ---------------------------------------------------------------------------------------------------------------------------------------- | ----------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [Applied Crypto](https://djao.math.uwaterloo.ca/w/CO_487:_Applied_Cryptography_%28Winter_2016%29)                                        | David Jao         | Looks like a really interesting course, and a great intro to crypto, but rather unlikely to benefit me too much if I keep doing QI stuff. Idk though hard to say, it could be a good start if I go into QI crypto stuff.                  |
| PSI QFT 1                                                                                                                                | Daniel Wohns      | I've always wanted to learn some QFT, and getting to do it at PI would be sweet, but it will definitely require to dust off some physics chops. Would be helpful if I want to do mathematical physics type stuff                          |
| [Category O](https://bwebster.notion.site/bwebster/Category-O-c7a1eb10f3f44d75b3b7b77fa2e97b8a)                                          | Ben Webster       | Would help me deepen my Lie/representation theory knowledge a lot. Could be cool to apply some of this knowledge to QI or see where it's been applied. Builds on previous course I took. Highly abstract and seems advanced very quickly. |
| [Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/)                                                                   | John Watrous      | If I want to continue in QI I feel like this is probably the most important class to take. Will almost definitely do this one unless I'm talked out of it.                                                                                |

---

## Workflow

All my classes thus far have required us to use Crowdmark to submit homework. In order to submit to crowdmark each homework question must be on a new page. To accomplish this I use the `pages` option on the [latex homework](https://github.com/natestemen/latex-homework/) template I've been working on. Once I'm finished I run

```bash
pdfseparate hwname.pdf hwname-%d.pdf
```

This separates the pages into their own document and I can upload them individually. Modern life...
