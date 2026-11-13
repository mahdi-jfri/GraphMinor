module

public import GraphMinor.GM01.SubdivisionSides
public import GraphMinor.GM01.AttachedRegions
public import GraphMinor.GM01.CombSpineCuts
import Lean.Elab.Tactic.Omega

/-!
# Ordered cuts in the subdivided comb

The spine cut property persists in the subdivision used on page 55 of
Graph Minors I. Lift the source side strictly after a cut by including
its incident replacing paths. Reachability from a later spine centre,
avoiding the cut centre, stays on this side. Earlier spine centres are
outside it, so they cannot be reached while avoiding the cut.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- An earlier spine centre cannot reach a later one in the subdivided
comb while avoiding an intermediate spine centre. This is the ordered
cut assertion behind the page-55 regions used in (1.1). -/
theorem comb_subdivision_earlier_not_mem_region {α β : Type*} {γ δ : ℕ}
    {N : Graph α β} {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ δ).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (i j t : Fin δ) (hji : j.val < i.val) (hit : i.val < t.val) :
    c ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩ ∉ vertexAvoidanceRegion N
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩) := by
  let D : Set (pathComb γ δ).verts :=
    {v | i.val < (pathCombSpineIndex v.val).val}
  let r : (pathComb γ δ).verts := ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩
  have hD : ∀ {a b : (pathComb γ δ).verts},
      (pathComb γ δ).coe.Adj a b → a ∈ D → b ≠ r → b ∈ D := by
    intro a b hab ha hbr
    exact pathComb_after_cut_adj_closed hab ha (fun h ↦ hbr (Subtype.ext h))
  let last : (pathComb γ δ).verts := ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩
  let earlier : (pathComb γ δ).verts := ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩
  have hlast : last ∈ D := hit
  have hearlier : earlier ≠ r := by
    intro heq
    have hval : j = i := Sum.inl.inj (congrArg Subtype.val heq)
    exact (Nat.ne_of_lt hji) (congrArg Fin.val hval)
  intro hmem
  have hside := vertexAvoidanceRegion_subdivision_subset_side
    hc hPN hE hPaths hInter D r hD last hlast hmem
  have hbad := (subdivision_centre_mem_side_iff hc hPaths D r hD hearlier).mp hside
  change i.val < j.val at hbad
  omega

/-- The regions beyond increasing spine cuts form a decreasing family
in the subdivided comb. This discharges the nesting condition used by
the successive-difference partition. -/
theorem comb_subdivision_regions_nested {α β : Type*} {γ δ : ℕ}
    {N : Graph α β} {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ δ).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (i j t : Fin δ) (hij : i.val < j.val) (hjt : j.val < t.val)
    (hlast : c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩ ∈ V(N)) :
    vertexAvoidanceRegion N
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩)
      (c ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩) ⊆
    vertexAvoidanceRegion N
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩) := by
  have hne : c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩ ≠
      c ⟨Sum.inl j, pathComb_spine_mem γ δ j⟩ := by
    intro heq
    have htj : t = j := Sum.inl.inj (congrArg Subtype.val (hc heq))
    have hval := congrArg Fin.val htj
    omega
  exact vertexAvoidanceRegion_subset_of_not_mem hlast hne
    (comb_subdivision_earlier_not_mem_region hc hPN hE hPaths hInter j i t hij hjt)

/-- Adjoining the separate root path does not change the regions beyond
spine cuts. Its only attachment is the first spine centre, which is
outside each such region (or is the deleted centre itself). -/
theorem comb_root_path_region_eq {α β : Type*} {γ δ : ℕ}
    {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ δ).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (i t : Fin δ) (hit : i.val < t.val)
    (hlast : c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩ ∈ V(N))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ δ (by omega)).root}) :
    vertexAvoidanceRegion (subgraphUnion G N R)
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩) =
    vertexAvoidanceRegion N
      (c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩) := by
  have hne : c ⟨Sum.inl t, pathComb_spine_mem γ δ t⟩ ≠
      c ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩ := by
    intro heq
    have hti : t = i := Sum.inl.inj (congrArg Subtype.val (hc heq))
    have hval := congrArg Fin.val hti
    omega
  apply vertexAvoidanceRegion_subgraphUnion_eq hN hR hlast hne hmeet
  by_cases hi : i.val = 0
  · have hroot : (rootedPathComb γ δ (by omega)).root =
        (⟨Sum.inl i, pathComb_spine_mem γ δ i⟩ : (pathComb γ δ).verts) := by
      apply Subtype.ext
      exact congrArg Sum.inl (Fin.ext hi.symm)
    rw [hroot]
    intro hm
    exact (vertexAvoidanceRegion_subset N _ _ hm).2 rfl
  · exact comb_subdivision_earlier_not_mem_region hc hPN hE hPaths hInter
      i ⟨0, by omega⟩ t (by change 0 < i.val; omega) hit

end GraphMinor.GM01
