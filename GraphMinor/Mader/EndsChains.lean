module

public import GraphMinor.Mader.ApexForest
public import GraphMinor.Kruskal.ChainSequence
import GraphMinor.Kruskal.InitialChains
import GraphMinor.Kruskal.TopologicalTransport
import GraphMinor.Minor.Basic

/-!
# Realizing subdivisions of graphs given by their edge ends

A chain with no internal vertices is the original edge. The explicit
isomorphism at length zero and the finite edge-subdivision sequence let
an embedded edge-chain graph witness topological containment directly.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

/-- The graph given by edge ends is isomorphic to its chain expansion
with no internal vertices. -/
noncomputable def endsInitialChainsIso {V E : Type*} (left right : E → V) :
    Iso (graphOfEnds left right) (edgeChains left right (fun _ ↦ 0)) where
  vertexEquiv := {
    toFun v := ⟨Sum.inl v.val, trivial⟩
    invFun v := match v with
      | ⟨Sum.inl x, _⟩ => ⟨x, Set.mem_univ _⟩
      | ⟨Sum.inr (_, k), hk⟩ => False.elim (Nat.not_lt_zero k hk)
    left_inv _ := rfl
    right_inv := by
      rintro ⟨x, hx⟩
      cases x with
      | inl v => rfl
      | inr p => exact (Nat.not_lt_zero p.2 hx).elim }
  edgeEquiv := {
    toFun e := ⟨(e.val, 0), Or.inl rfl⟩
    invFun d := ⟨d.val.1, Set.mem_univ _⟩
    left_inv _ := rfl
    right_inv := by
      rintro ⟨⟨e, j⟩, hj⟩
      have hj' : j = 0 := by
        change j = 0 ∨ j % 2 = 1 ∧ j < 0 at hj
        omega
      exact Subtype.ext (Prod.ext rfl hj'.symm) }
  isLink_iff e x y := by
    change ((x.val = left e.val ∧ y.val = right e.val) ∨
        (x.val = right e.val ∧ y.val = left e.val)) ↔
      (edgeChains left right (fun _ ↦ 0)).IsLink (e.val, 0) (Sum.inl x.val) (Sum.inl y.val)
    rw [edgeChains_zero_isLink]

/-- Injective link-preserving maps of a chain expansion into a target
give topological containment of the graph specified by the original ends. -/
theorem isTopologicalMinor_of_ends_chainEmbedding {V E α β : Type*}
    [Finite V] [Finite E] (left right : E → V) (n : E → ℕ) (G : Graph α β)
    (vertices : V(edgeChains left right n) ↪ α)
    (edges : E(edgeChains left right n) ↪ β)
    (hvertices : ∀ x, vertices x ∈ V(G))
    (hlinks : ∀ (d : E(edgeChains left right n)) (x y : V(edgeChains left right n)),
      (edgeChains left right n).IsLink d.val x.val y.val →
        G.IsLink (edges d) (vertices x) (vertices y)) :
    GM04.IsTopologicalMinor (graphOfEnds left right) G := by
  classical
  let := Fintype.ofFinite E
  let K := renameGraph (edgeChains left right n) vertices edges
  have hKG : K ≤ G := by
    constructor
    · rintro x ⟨a, rfl⟩
      exact hvertices a
    · rintro d x y ⟨e, a, b, h, rfl, rfl, rfl⟩
      exact hlinks e a b h
  have hchain := edgeChains_isTopologicalMinor left right n
  have hsource := isTopologicalMinor_iso_source (endsInitialChainsIso left right) hchain
  exact isTopologicalMinor_mono_target hKG
    (isTopologicalMinor_iso_target (renameGraphIso _ vertices edges) hsource)

end GraphMinor.Mader
