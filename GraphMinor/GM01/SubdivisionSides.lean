module

public import GraphMinor.GM09.Basic
public import GraphMinor.GM01.VertexAvoidanceRegions
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Sides of a cut in a subdivision

To transfer the spine cuts on page 55 of Graph Minors I, put a replacing
path on a side whenever its source edge has an end on that side. A
branch centre on one of these paths is one of its two ends. Thus, away
from the cut centre, membership on a side agrees with membership of the
source vertex. Distinct replacing paths meet only at branch centres.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- Vertices on a chosen source side and on replacing paths incident
with that side. This is a proof construction for transferring the
page-55 spine cuts to the subdivided comb. -/
def subdivisionSide {α β ν : Type*} {S : SimpleGraph ν}
    (c : ν → α) (P : S.edgeSet → Graph α β) (D : Set ν) : Set α :=
  c '' D ∪ ⋃ e : S.edgeSet, ⋃ (_ : ∃ v ∈ D, v ∈ e.val), V(P e)

/-- A centre on a replacing path is an end of the corresponding source
edge. The injectivity of the centre map identifies which end. -/
theorem subdivision_centre_mem_path_iff {α β ν : Type*} {S : SimpleGraph ν}
    {c : ν → α} (hc : Function.Injective c) {P : S.edgeSet → Graph α β}
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b}) (e : S.edgeSet) (v : ν) :
    c v ∈ V(P e) ↔ v ∈ e.val := by
  obtain ⟨a, b, he, hRange⟩ := hPaths e
  constructor
  · intro hv
    have hm : c v ∈ ({c a,c b} : Set α) := hRange ▸ ⟨hv, mem_range_self v⟩
    rcases hm with h | h
    · rw [he]
      exact Sym2.mem_iff.mpr (Or.inl (hc h))
    · rw [he]
      exact Sym2.mem_iff.mpr (Or.inr (hc h))
  · intro hv
    rw [he, Sym2.mem_iff] at hv
    have hinc : c v ∈ ({c a,c b} : Set α) := by
      rcases hv with h | h
      · exact Or.inl (congrArg c h)
      · exact Or.inr (congrArg c h)
    exact ((hRange.symm ▸ hinc) : c v ∈ V(P e) ∩ range c).1

/-- Away from the cut, a centre belongs to the lifted side exactly when
its source vertex belongs to the source side. The only source edges
leaving that side use the cut vertex. -/
theorem subdivision_centre_mem_side_iff {α β ν : Type*} {S : SimpleGraph ν}
    {c : ν → α} (hc : Function.Injective c) {P : S.edgeSet → Graph α β}
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b}) (D : Set ν) (r : ν)
    (hD : ∀ {a b}, S.Adj a b → a ∈ D → b ≠ r → b ∈ D)
    {v : ν} (hv : v ≠ r) : c v ∈ subdivisionSide c P D ↔ v ∈ D := by
  constructor
  · intro h
    rcases h with ⟨w, hw, heq⟩ | h
    · exact hc heq ▸ hw
    · obtain ⟨e, h⟩ := mem_iUnion.mp h
      obtain ⟨⟨w, hw, hwe⟩, hve⟩ := mem_iUnion.mp h
      have hve' := (subdivision_centre_mem_path_iff hc hPaths e v).mp hve
      by_cases hwv : w = v
      · exact hwv ▸ hw
      · have heq := (Sym2.mem_and_mem_iff hwv).mp ⟨hwe, hve'⟩
        have hadj : S.Adj w v := by
          have hm := e.property
          rw [heq] at hm
          exact hm
        exact hD hadj hw hv
  · intro hvD
    exact Or.inl ⟨v, hvD, rfl⟩

/-- An edge can leave a lifted source side only through the cut centre.
An edge of the subdivision lies on a replacing path. If that path differs
from the one witnessing side membership, their common vertex is a centre,
so the source-side cut property decides which side its edge belongs to. -/
theorem subdivisionSide_adj_closed {α β ν : Type*} {S : SimpleGraph ν}
    {N : Graph α β} {c : ν → α} (hc : Function.Injective c)
    {P : S.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (D : Set ν) (r : ν)
    (hD : ∀ {a b}, S.Adj a b → a ∈ D → b ≠ r → b ∈ D)
    {x y : α} (hx : x ∈ subdivisionSide c P D) (hxne : x ≠ c r)
    (hxy : N.Adj x y) : y ∈ subdivisionSide c P D := by
  obtain ⟨edge, hlink⟩ := hxy
  have he := hlink.edge_mem
  rw [hE] at he
  obtain ⟨f, hef⟩ := mem_iUnion.mp he
  have hlf : (P f).IsLink edge x y := ((hPN f).isLink_iff hef).mpr hlink
  have hselect : ∃ v ∈ D, v ∈ f.val := by
    have hxAll := hx
    rcases hx with ⟨v, hv, rfl⟩ | hx
    · exact ⟨v, hv, (subdivision_centre_mem_path_iff hc hPaths f v).mp hlf.left_mem⟩
    · obtain ⟨e, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hchosen, hxe⟩ := mem_iUnion.mp hx
      by_cases hef' : e = f
      · exact hef' ▸ hchosen
      · obtain ⟨v, rfl⟩ := hInter e f hef' ⟨hxe, hlf.left_mem⟩
        have hvne : v ≠ r := fun h ↦ hxne (congrArg c h)
        have hvD := (subdivision_centre_mem_side_iff hc hPaths D r hD hvne).mp hxAll
        exact ⟨v, hvD, (subdivision_centre_mem_path_iff hc hPaths f v).mp hlf.left_mem⟩
  exact Or.inr (mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hselect, hlf.right_mem⟩⟩)

/-- Reachability from a centre on a source side, avoiding the cut centre,
stays on the lifted side. This transfers source cuts to the subdivision. -/
theorem vertexAvoidanceRegion_subdivision_subset_side {α β ν : Type*}
    {S : SimpleGraph ν} {N : Graph α β} {c : ν → α}
    (hc : Function.Injective c) {P : S.edgeSet → Graph α β}
    (hPN : ∀ e, P e ≤ N) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (D : Set ν) (r : ν)
    (hD : ∀ {a b}, S.Adj a b → a ∈ D → b ≠ r → b ∈ D)
    (t : ν) (ht : t ∈ D) :
    vertexAvoidanceRegion N (c t) (c r) ⊆ subdivisionSide c P D := by
  intro x hx
  have hr := hx.2
  induction hr with
  | refl => exact Or.inl ⟨t, ht, rfl⟩
  | @tail a b hr hstep ih =>
    obtain ⟨edge, he⟩ := hstep
    have hxne : a ≠ c r := by
      have hm := he.left_mem
      rw [vertexSet_deleteVerts] at hm
      exact hm.2
    exact subdivisionSide_adj_closed hc hPN hE hPaths hInter D r hD (ih ⟨he.left_mem, hr⟩) hxne
      ⟨edge, he.mono Graph.deleteVerts_le⟩

end GraphMinor.GM01
