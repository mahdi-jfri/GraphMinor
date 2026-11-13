module

public import GraphMinor.GM02.TopologicalContainment

/-!
# Changing the ambient edge names

The finite patterns in II (4.8) use a standard countable edge type.
A bijection of ambient edge names retains vertices and incidence.
It gives an isomorphic graph and preserves the subgraph relation.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set

/-- Rename every edge by a fixed ambient bijection. -/
def relabelEdges {A B C : Type*} (e : B ≃ C) (G : Graph A B) : Graph A C where
  vertexSet := V(G)
  edgeSet := e.symm ⁻¹' E(G)
  IsLink f a b := G.IsLink (e.symm f) a b
  isLink_symm f _ := ⟨fun _ _ h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ h h' => h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink f := G.edge_mem_iff_exists_isLink (e.symm f)
  left_mem_of_isLink := fun _ _ _ h => h.left_mem

/-- The edge bijection and identity vertex map give the canonical relabelling isomorphism. -/
def relabelEdgesIso {A B C : Type*} (e : B ≃ C) (G : Graph A B) : Iso G (relabelEdges e G) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := {
    toFun := fun f => ⟨e f.val, by simpa only [relabelEdges, Set.mem_preimage, Equiv.symm_apply_apply] using f.property⟩
    invFun := fun f => ⟨e.symm f.val, f.property⟩
    left_inv := fun f => by apply Subtype.ext; exact e.symm_apply_apply f.val
    right_inv := fun f => by apply Subtype.ext; exact e.apply_symm_apply f.val }
  isLink_iff := by
    intro f a b
    change G.IsLink f.val a.val b.val ↔ G.IsLink (e.symm (e f.val)) a.val b.val
    rw [Equiv.symm_apply_apply]

/-- Renaming ambient edge names preserves subgraph inclusion. -/
theorem relabelEdges_mono {A B C : Type*} (e : B ≃ C) {G H : Graph A B}
    (h : G ≤ H) : relabelEdges e G ≤ relabelEdges e H :=
  ⟨h.vertexSet_mono, fun _ _ _ hlink => h.isLink_mono hlink⟩

/-- Relabelling by the inverse bijection recovers the original graph. -/
theorem relabelEdges_symm {A B C : Type*} (e : B ≃ C) (G : Graph A B) :
    relabelEdges e.symm (relabelEdges e G) = G := by
  apply Graph.ext (G₁ := relabelEdges e.symm (relabelEdges e G)) (G₂ := G) rfl
  intro f a b
  change G.IsLink (e.symm (e f)) a b ↔ G.IsLink f a b
  rw [Equiv.symm_apply_apply]

end GraphMinor.GM02
