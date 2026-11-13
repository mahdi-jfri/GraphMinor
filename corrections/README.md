# Corrections to the papers

While formalizing the Graph Minors series, we found places where a paper is wrong as printed. In
each case the Lean library proves a corrected form. This folder describes every correction, one
file per paper.

Each correction has one of five kinds.

* **Misprint.** A wrong symbol, index or word, where the intended text is plain from the context.
* **Statement mistake.** A numbered result, or a claim made in the text outside a proof, is false
  as printed, and not only in a trivial case. The file gives a counterexample and the corrected
  form, and checks that the later uses of the result still work.
* **Degenerate case.** A statement fails only in a trivial case, such as an empty graph or a
  parameter equal to $0$. The correction adds a hypothesis that excludes the case, or handles it.
* **Proof gap.** A step of a proof does not follow as written, or a claim inside a proof is false.
  The file gives the missing argument. In most cases the statement holds as printed.
* **Missing proof.** The paper omits a proof, leaves it to the reader, says that it is easy, or
  only sketches it. The file gives the argument that the Lean proof uses.

The corrected copies show the same five kinds in colour. Each note in a copy, and each item in the
list on its first page, begins with the kind.

None of the corrections changes the statement of a main result of the series. Each entry gives
the place in the paper (result, page and, where it helps, the claim in the proof), what goes wrong
or what is missing, the correction or the added proof, and the Lean theorem that proves the
corrected form. The repository
[GraphMinorPapers](https://github.com/hajiaghayi/GraphMinorPapers) has copies of the papers with
these corrections marked and the missing proofs added in place.

| Paper | Misprints | Statement mistakes | Degenerate cases | Proof gaps | Missing proofs | Total |
| --- | --- | --- | --- | --- | --- | --- |
| [I](GM01.md) | 6 | 0 | 3 | 0 | 5 | 14 |
| [II](GM02.md) | 2 | 2 | 0 | 1 | 5 | 10 |
| [III](GM03.md) | 1 | 0 | 1 | 0 | 5 | 7 |
| [IV](GM04.md) | 1 | 1 | 0 | 0 | 5 | 7 |
| [V](GM05.md) | 2 | 2 | 3 | 0 | 3 | 10 |
| [VI](GM06.md) | 0 | 2 | 0 | 1 | 5 | 8 |
| [VII](GM07.md) | 2 | 4 | 0 | 5 | 4 | 15 |
| [VIII](GM08.md) | 4 | 1 | 1 | 3 | 4 | 13 |
| [IX](GM09.md) | 1 | 0 | 1 | 3 | 4 | 9 |
| [X](GM10.md) | 1 | 0 | 0 | 1 | 3 | 5 |
| [XI](GM11.md) | 0 | 3 | 0 | 0 | 1 | 4 |
| [XII](GM12.md) | 2 | 1 | 3 | 6 | 3 | 15 |
| [XIII](GM13.md) | 0 | 0 | 0 | 7 | 11 | 18 |
| [XIV](GM14.md) | 2 | 1 | 0 | 4 | 7 | 14 |
| [XV](GM15.md) | 10 | 2 | 1 | 4 | 2 | 19 |
| [XVI](GM16.md) | 19 | 1 | 0 | 3 | 2 | 25 |
| [XVII](GM17.md) | 12 | 2 | 0 | 2 | 2 | 18 |
| [XVIII](GM18.md) | 5 | 0 | 0 | 1 | 3 | 9 |
| [XIX](GM19.md) | 6 | 2 | 0 | 4 | 16 | 28 |
| [XX](GM20.md) | 2 | 1 | 0 | 3 | 1 | 7 |
| [XXI](GM21.md) | 31 | 4 | 1 | 12 | 14 | 62 |
| [XXII](GM22.md) | 10 | 1 | 0 | 0 | 1 | 12 |
| **I–XXII** | **119** | **30** | **14** | **60** | **106** | **329** |
| [RST94](RST94.md) | 1 | 0 | 0 | 3 | 0 | 4 |
| [HP25](HP25.md) | 1 | 1 | 0 | 3 | 0 | 5 |


The page numbers are those of the journal, except for Graph Minors XXI, whose copy follows the
authors' version of April 18, 2011. Two other works that the series uses are formalized as well and
have corrections here: [RST94.md](RST94.md) for N. Robertson, P. D. Seymour and R. Thomas, *Quickly
excluding a planar graph*, J. Combin. Theory Ser. B 62 (1994), 323–348, and [HP25.md](HP25.md) for
S. Humeau and D. Pous, *On the two paths theorem and the two disjoint paths problem*,
arXiv:2505.16431v2.
