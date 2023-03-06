# courses

A repo for my coursework as a ~phd~ masters student at the University of Waterloo in the applied math department, with a specialization in quantum information.

I mostly took courses pretty seriously, but I know grades during a grad degree basically don't matter.
For that reason I tried not to spend crazy amounts of time on homeworks, but if I did, chances were I was fiddling with LaTeX, not doing homework.
I learned a lot of cool TeX things while writing all these up, like drawing quantum circuit diagrams, plotting functions, and doing things with colors.

## Year 1 (2020-2021)

### Fall 2020

| Course                                                                                                                                     | Professor                                                       | Directory      |
| ------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------- | -------------- |
| Numerical Analysis                                                                                                                         | [Hans De Sterck](http://www.hansdesterck.net/)                  | [`num`](./num) |
| [Advanced Quantum Theory](https://uwaterloo.ca/physics-of-information-lab/teaching/advanced-quantum-theory-amath-473673-phys454-fall-2020) | [Achim Kempf](https://uwaterloo.ca/physics-of-information-lab/) | [`aqt`](.aqt)  |
| [Quantum Info. Processing](http://cleve.iqc.uwaterloo.ca/qic710/index.html)                                                                | [Richard Cleve](http://cleve.iqc.uwaterloo.ca/)                 | [`qip`](./qip) |

### Winter 2021

| Course                    | Professor                                                                    | Directory      |
| ------------------------- | ---------------------------------------------------------------------------- | -------------- |
| Open Quantum Systems      | [Joseph Emerson](https://services.iqc.uwaterloo.ca/people/profile/jemerson/) | [`oqs`](./oqs) |
| Lie Groups & Lie Algebras | [Da Rong Cheng](https://sites.google.com/view/daren-cheng)                   | [`lie`](./lie) |

### Summer 2021

| Course                                                                                | Professor                                            | Directory      |
| ------------------------------------------------------------------------------------- | ---------------------------------------------------- | -------------- |
| [Software Verification using Proof Assistants](https://cs.uwaterloo.ca/~plragde/747/) | [Prabhakar Ragde](https://cs.uwaterloo.ca/~plragde/) | [`swv`](./swv) |

## Year 2 (2021-2022)

### Fall 2021

| Course                                                                                                                                 | Professor                                                       | Directory      |
| -------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------- | -------------- |
| [Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/)                                                                 | [John Watrous](https://cs.uwaterloo.ca/~watrous/)               | [`tqi`](./tqi) |
| [~~General Relativity for Cosmology~~ (dropped)](https://uwaterloo.ca/poi/teaching/general-relativity-cosmology-amath875phys786-f2021) | [Achim Kempf](https://uwaterloo.ca/physics-of-information-lab/) | [`gr`](./gr)   |

### Winter 2021

| Course                          | Professor                                           | Directory      |
| ------------------------------- | --------------------------------------------------- | -------------- |
| Logic and Computability (audit) | [Jason Bell](https://www.math.uwaterloo.ca/~jpbell) | [`log`](./log) |

---

## Workflow

All my classes thus far have required us to use Crowdmark to submit homework. In order to submit to crowdmark each homework question must be on a new page. To accomplish this I use the `pages` option on the [latex homework](https://github.com/natestemen/latex-homework/) template I've been working on. Once I'm finished I run

```bash
pdfseparate hwname.pdf hwname-%d.pdf
```

This separates the pages into their own document and I can upload them individually. Modern life...

A command to run to see which homeworks have given me the most trouble... kind of.

```
git log --name-only --pretty=format: | sort | uniq -c | sort -nr
```
