module

public import GraphMinor.GM01.ForestModelExtension
import GraphMinor.GM01.TreeSubgraph
import GraphMinor.GM16.ForestPacking

/-!
# Every finite forest is a minor of a branching tree

Graph Minors I, proof of (1.1), page 51, uses the elementary fact that each
finite forest is a minor of some `Y_ℓ`. We remove a vertex with at most one
neighbour and restore it by the branch-set extension construction. Each
branch set retains a vertex on the outer level. One more outer vertex is
kept unused, so isolated vertices can also be restored.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

variable {α : Type*}

private theorem forestTree_model_aux (n : ℕ) :
    ∀ (H : (⊤ : SimpleGraph α).Subgraph), H.verts.Finite → H.coe.IsAcyclic →
      H.verts.ncard = n →
    ∃ (K : α → (⊤ : SimpleGraph ForestTreeVertex).Subgraph)
      (r : α → ForestTreeVertex) (spare : ForestTreeVertex),
      (∀ u ∈ H.verts, K u ≤ forestTree n ∧ (K u).Connected ∧
        r u ∈ (K u).verts ∧ forestTreeDepth (r u) = n) ∧
      (∀ u ∈ H.verts, ∀ v ∈ H.verts, u ≠ v → Disjoint (K u).verts (K v).verts) ∧
      (∀ u v, H.Adj u v →
        ∃ a ∈ (K u).verts, ∃ b ∈ (K v).verts, (forestTree n).Adj a b) ∧
      forestTreeDepth spare = n ∧ (∀ u ∈ H.verts, spare ∉ (K u).verts) := by
  classical
  induction n with
  | zero =>
    intro H hfin hacyc hcard
    have hempty : H.verts = ∅ := (Set.ncard_eq_zero hfin).mp hcard
    have hnone : ∀ u ∈ H.verts, False := by simp [hempty]
    refine ⟨fun _ ↦ ⊥, fun _ ↦ none, none, ?_, ?_, ?_, rfl, ?_⟩
    · intro u hu
      exact False.elim (hnone u hu)
    · intro u hu
      exact False.elim (hnone u hu)
    · intro u v huv
      exact False.elim (hnone u huv.fst_mem)
    · intro u hu
      exact False.elim (hnone u hu)
  | succ n ih =>
    intro H hfin hacyc hcard
    have hnonempty : H.verts.Nonempty := (Set.ncard_pos hfin).mp (by omega)
    let : Finite H.verts := hfin.to_subtype
    let : Nonempty H.verts := ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    obtain ⟨x, hxleaf⟩ := GM16.exists_leaf_of_finite_forest hacyc
    have hleaf : ∀ u v, H.Adj x.val u → H.Adj x.val v → u = v := by
      intro u v hxu hxv
      have heq := hxleaf
        (show (⟨u, hxu.snd_mem⟩ : H.verts) ∈ H.coe.neighborSet x from hxu)
        (show (⟨v, hxv.snd_mem⟩ : H.verts) ∈ H.coe.neighborSet x from hxv)
      exact congrArg Subtype.val heq
    let H' := H.deleteVerts {x.val}
    have hfin' : H'.verts.Finite := hfin.subset H.deleteVerts_le.1
    have hacyc' : H'.coe.IsAcyclic := isAcyclic_of_le hacyc H.deleteVerts_le
    have hcard' : H'.verts.ncard = n := by
      change (H.verts \ {x.val}).ncard = n
      rw [Set.ncard_sdiff_singleton_of_mem x.property, hcard]
      exact Nat.add_sub_cancel n 1
    obtain ⟨K, r, spare, hK, hdisj, hedge, hsd, hspare⟩ := ih H' hfin' hacyc' hcard'
    by_cases hneighbor : ∃ u, H.Adj x.val u
    · obtain ⟨u, hxu⟩ := hneighbor
      have hu : u ∈ H'.verts := ⟨hxu.snd_mem, hxu.ne.symm⟩
      apply forestTree_model_add_vertex H K r spare hK hdisj hedge hsd hspare
        (r u) (hK u hu).2.2.2
      intro v hxv
      rw [hleaf u v hxu hxv]
    · apply forestTree_model_add_vertex H K r spare hK hdisj hedge hsd hspare spare hsd
      intro v hxv
      exact False.elim (hneighbor ⟨v, hxv⟩)

/-- The elementary forest-minor observation in Graph Minors I, proof of
(1.1), page 51, in the simple-graph representation. A forest with `n`
vertices has a minor model in `Y_n`. The proof removes and restores leaves,
using the library's finite-forest leaf lemma. -/
theorem isIsoMinor_forestTree_of_isAcyclic
    (H : (⊤ : SimpleGraph α).Subgraph) (hfin : H.verts.Finite)
    (hacyc : H.coe.IsAcyclic) :
    IsIsoMinor (toGraph H) (forestTreeGraph H.verts.ncard) := by
  obtain ⟨K, r, spare, hK, hdisj, hedge, hsd, hspare⟩ :=
    forestTree_model_aux H.verts.ncard H hfin hacyc rfl
  exact isIsoMinor_toGraph_of_connected_subgraphs hfin
    (forestTree_vertices_finite _) K (fun u hu ↦ (hK u hu).1)
    (fun u hu ↦ (hK u hu).2.1) hdisj (fun {u v} huv ↦ hedge u v huv)

/-- The proof of Graph Minors I, (1.1), page 51, chooses an odd depth.
Increasing the depth of the model to `2n + 1` makes this choice explicit. -/
theorem exists_odd_forestTree_minor_of_isAcyclic
    (H : (⊤ : SimpleGraph α).Subgraph) (hfin : H.verts.Finite)
    (hacyc : H.coe.IsAcyclic) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ Odd ℓ ∧ IsIsoMinor (toGraph H) (forestTreeGraph ℓ) := by
  let ℓ := 2 * H.verts.ncard + 1
  refine ⟨ℓ, Nat.zero_lt_succ _, ⟨H.verts.ncard, rfl⟩, ?_⟩
  exact (isIsoMinor_forestTree_of_isAcyclic H hfin hacyc).trans
    (isIsoMinor_toGraph_of_le (forestTree_mono (show H.verts.ncard ≤ ℓ by omega)))

end GraphMinor.GM01
