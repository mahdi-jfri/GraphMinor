module

public import GraphMinor.Thomason.NeighborBranches
import GraphMinor.Thomason.CliqueBranchesOfMinor
import GraphMinor.GM01.MinorNonempty

/-!
# Extending a neighbourhood clique minor

Recover connected branches from a clique minor inside a neighbourhood.
The neighbourhood centre is outside all these branches and adjacent to
each one, so it adds a clique vertex. This is the step used twice in
Thomason's Lemma 1 (1984), p. 262.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset Graph Set
universe u

/-- A clique minor inside a neighbourhood extends by its centre to a
clique minor with one more vertex, as in Thomason's Lemma 1, p. 262. -/
theorem clique_isIsoMinor_of_neighbor_minor {V : Type u} [Fintype V]
    (G : SimpleGraph V) (u : V) {q : ℕ}
    (hm : IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q)))
      (Graph.ofSimpleGraph (G.induce (G.neighborSet u)))) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  classical
  cases q with
  | zero =>
    apply clique_isIsoMinor_of_neighbor_branches G u (Fin.elim0 : Fin 0 → Finset (G.neighborSet u))
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  | succ q =>
    obtain ⟨w, _⟩ := GM01.minor_vertexSet_nonempty hm ⟨0, mem_univ _⟩
    let : Nonempty (G.neighborSet u) := ⟨w⟩
    obtain ⟨T, hconn, hdis, hadj⟩ := exists_branches_of_clique_isIsoMinor
      (G.induce (G.neighborSet u)) hm
    exact clique_isIsoMinor_of_neighbor_branches G u T hconn hdis hadj

end GraphMinor.Thomason
