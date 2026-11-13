module

public import GraphMinor.GM02.EdgeRelabellingSuppression

/-!
# Topological containment is independent of ambient edge names

Transport every suppression through the edge-name bijection, keeping
the same surviving vertices. The final isomorphism keeps its vertex
map. For an isomorphic contained copy, rename that copy's edges too;
the inverse bijection gives the reverse implication.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Relation

/-- Apply the same edge renaming to both graphs of an isomorphism, retaining its vertex map. -/
def relabelEdgesIsoMap {A B C : Type*} {H L : Graph A B} (e : B ≃ C)
    (φ : Iso H L) : Iso (relabelEdges e H) (relabelEdges e L) where
  vertexEquiv := φ.vertexEquiv
  edgeEquiv := (relabelEdgesIso e H).edgeEquiv.symm.trans
    (φ.edgeEquiv.trans (relabelEdgesIso e L).edgeEquiv)
  isLink_iff := by
    intro f a b
    change H.IsLink (e.symm f.val) a.val b.val ↔
      L.IsLink (e.symm (e (φ.edgeEquiv ⟨e.symm f.val, f.property⟩).val))
        (φ.vertexEquiv a).val (φ.vertexEquiv b).val
    rw [Equiv.symm_apply_apply]
    exact φ.isLink_iff ⟨e.symm f.val, f.property⟩ a b


/-- Rename the ambient edges throughout a topological containment witness. -/
theorem TopologicallyContains.relabelEdges {A B C : Type*} {G H : Graph A B}
    (h : TopologicallyContains G H) (e : B ≃ C) :
    TopologicallyContains (GraphMinor.GM02.relabelEdges e G) (GraphMinor.GM02.relabelEdges e H) := by
  obtain ⟨K, hK, L, hs, φ, hφ⟩ := h
  have hs' : ReflTransGen IsSuppression (GraphMinor.GM02.relabelEdges e K)
      (GraphMinor.GM02.relabelEdges e L) := by
    clear φ hφ
    induction hs with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail (hstep.relabelEdges e)
  exact ⟨GraphMinor.GM02.relabelEdges e K, relabelEdges_mono e hK,
    GraphMinor.GM02.relabelEdges e L, hs', relabelEdgesIsoMap e φ, hφ⟩

/-- Isomorphic topological containment of a fixed target does not depend on host edge names. -/
theorem exists_topologicallyContains_iso_relabelEdges_iff {A B C D E : Type*}
    (G : Graph A B) (J : Graph D E) (e : B ≃ C) :
    (∃ L : Graph A B, TopologicallyContains G L ∧ Nonempty (Iso J L)) ↔
      ∃ L : Graph A C, TopologicallyContains (relabelEdges e G) L ∧ Nonempty (Iso J L) := by
  constructor
  · rintro ⟨L, ht, ⟨φ⟩⟩
    exact ⟨relabelEdges e L, ht.relabelEdges e, ⟨φ.trans (relabelEdgesIso e L)⟩⟩
  · rintro ⟨L, ht, ⟨φ⟩⟩
    have ht' := ht.relabelEdges e.symm
    rw [relabelEdges_symm] at ht'
    exact ⟨relabelEdges e.symm L, ht', ⟨φ.trans (relabelEdgesIso e.symm L)⟩⟩

end GraphMinor.GM02
