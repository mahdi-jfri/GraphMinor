module

public import GraphMinor.GM08.Defs

/-!
# Graph Minors VIII, Section 1: Introduction (pages 255–257)

This file holds a fact used in Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- `finite_of_isGraphAntichain`: every antichain of finite graphs is finite, proved from the graph
  minor theorem `GraphMinor.GM20.graph_minor_theorem_assembled` (`GraphMinor/GM20/Assembled.lean`).

The numbered results (1.1) and (1.2) are proved in `GraphMinor/GM08/Section1Proof.lean`, by the
paper's route through (6.1). The fact here is used only in Section 2, for the finiteness of
$S(P)$ that the paper asserts as a consequence of Wagner's conjecture.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology Graph GraphMinor.Surface

universe u v w

/-- Every antichain of finite graphs is finite, proved directly from the graph minor theorem
`GraphMinor.GM20.graph_minor_theorem_assembled`. -/
theorem finite_of_isGraphAntichain {α : Type u} {β : Type v}
    {A : Set (Graph α β)} (hA : IsGraphAntichain A) :
    A.Finite := by
  by_contra hInf
  have hInf' : A.Infinite := hInf
  let e : ℕ ↪ A := hInf'.natEmbedding
  let G : ℕ → Graph α β := fun n => (e n).1
  have hfin : ∀ n, V(G n).Finite ∧ E(G n).Finite := fun n => hA.1 (G n) (e n).2
  obtain ⟨i, j, hij, hminor⟩ :=
    GraphMinor.GM20.graph_minor_theorem_assembled G (fun n => (hfin n).1) (fun n => (hfin n).2)
  have hne : G i ≠ G j := fun heq => hij.ne (e.injective (Subtype.ext heq))
  exact hA.2 (G i) (e i).2 (G j) (e j).2 hne hminor

end GraphMinor.GM08
