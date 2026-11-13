module

public import GraphMinor.GM22.Defs

/-!
# Results Cited in Graph Minors XXII

This file states as a `Prop` the result from an earlier paper of the Graph Minors series that is
used in N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage
problems*, J. Combin. Theory Ser. B **102** (2012) 530–563. It is proved in `GraphMinor/GM21/`, and
`GraphMinor/GM22/GM21Proved.lean` passes the proof to XXII:

* **Graph Minors XXI** (*Graphs with unique linkages*, JCTB **99** (2009) 583–616):
  - `GM21Theorem11Statement`, Theorem 1.1 (stated as **1.1** in Graph Minors XXII, Section 1,
    page 531), used in the proof of **2.1** (Section 2, page 532).

All other results from earlier papers cited in Graph Minors XXII are already proved in this
library:
* Graph Minors VI, (3.6): `GraphMinor.GM06.theorem_3_6_proof` (`GraphMinor/GM06/DualExists.lean`), used
  in **3.3** (page 535);
* Graph Minors XIV, (5.5): `GraphMinor.GM14.theorem_5_5_proof` (`GraphMinor/GM14/Section5.lean`), used
  in **5.2** (page 540);
* Graph Minors XIV, (6.5): `GraphMinor.GM14.theorem_6_5_proof` (`GraphMinor/GM14/Section6.lean`), used
  in Claim (2) of **8.3** (page 560);
* Graph Minors XIV, (7.5): `GraphMinor.GM14.theorem_7_5_proof` (`GraphMinor/GM14/Section7a.lean`), used
  in Claim (5) of **5.3** (page 541);
* Graph Minors XIV, (9.2): `GraphMinor.GM14.theorem_9_2_proof` / `GraphMinor.GM14.full_of_9_2`
  (`GraphMinor/GM14/Section9a.lean`), used in **5.1** (page 539).
* Seymour and Thomas, *Graph searching, and a min-max theorem for tree-width*, JCTB **58** (1993)
  22–33, Theorem 1.4 (the easy direction: a graph admitting a haven of order $h$ has tree-width at
  least $h - 1$), proved directly in `GraphMinor/GM22/Section3.lean` and used in **3.2** (page 535).
-/

@[expose] public section

namespace GraphMinor.GM22

open Graph

universe u v

/-- **Graph Minors XXI, (1.1)** (*Graphs with unique linkages*, Section 1; stated as **1.1** in
Graph Minors XXII, Section 1, page 531):
"For every integer $p \ge 0$ there exists $w \ge 0$ such that every graph with a vital $p$-linkage
has tree-width $\le w$." -/
def GM21Theorem11Statement : Prop :=
  ∀ p : ℕ, ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β),
    V(G).Finite → E(G).Finite → IsVitalPLinkage G L p → TreeWidthLE G w

end GraphMinor.GM22
