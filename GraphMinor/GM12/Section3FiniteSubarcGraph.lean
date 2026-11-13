module

public import GraphMinor.GM12.Section3AddSubarc

/-!
# The finite graph made from retained original subarcs

The homotopy-preserving rerouting used in the Section 8 reduction of
XII (3.1), page 245, leaves finitely many segments of one original arc.
Each has finite contact with the first circle. Add them one at a time.
The interval calculation supplies finite connectedness off the growing
graph at each step. This constructs a finite graph inside the original
circle union arc, without assuming finite intersections of the two.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A finite family of original subarcs, each with finite contact
with a fixed finite graph carrier, can all be added to that graph. -/
theorem exists_graph_union_finite_subarcs
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    {p : unitInterval → S} (hp : IsArcMap p) {F V : Set S} {E : Set (Set S)}
    (hG : IsGraph V E) (hgr : gr V E = F) (J : Finset ι) (a b : ι → unitInterval)
    (hcontact : ∀ i ∈ J, ((p '' Icc (a i) (b i)) ∩ F).Finite) :
    ∃ V' E', V ⊆ V' ∧ IsGraph V' E' ∧ gr V' E' = F ∪ ⋃ i ∈ J, p '' Icc (a i) (b i) := by
  classical
  revert hcontact
  induction J using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨V, E, subset_rfl, hG, ?_⟩
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty] using hgr
  | @insert i J hi ih =>
    intro hcontact
    obtain ⟨V₁, E₁, hVV₁, hG₁, hgr₁⟩ := ih (fun j hj => hcontact j (Finset.mem_insert_of_mem hj))
    obtain ⟨V₂, E₂, hV₁₂, hG₂, hgr₂⟩ := exists_graph_add_subarc_of_finite_contacts hp hG₁ J a b
      hgr₁ (a i) (b i) (hcontact i (Finset.mem_insert_self i J))
    refine ⟨V₂, E₂, hVV₁.trans hV₁₂, hG₂, ?_⟩
    have hU : (⋃ j ∈ insert i J, p '' Icc (a j) (b j)) =
        (p '' Icc (a i) (b i)) ∪ ⋃ j ∈ J, p '' Icc (a j) (b j) := by
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    rw [hgr₂, hgr₁, hU]
    ac_rfl

/-- A circle together with finitely many subarcs of one injective arc
has a finite graph presentation if each subarc has finite contact with
the circle. The subarcs may overlap one another. -/
theorem exists_graph_circle_union_finite_subarcs
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    {F : Set S} (hF : IsOArc F) {p : unitInterval → S} (hp : IsArcMap p)
    (J : Finset ι) (a b : ι → unitInterval)
    (hcontact : ∀ i ∈ J, ((p '' Icc (a i) (b i)) ∩ F).Finite) :
    ∃ V E, IsGraph V E ∧ gr V E = F ∪ ⋃ i ∈ J, p '' Icc (a i) (b i) := by
  have hzero : gr (∅ : Set S) ∅ = ∅ := by simp [gr]
  have hfin : FinConn (F \ gr (∅ : Set S) ∅) := by
    rw [hzero, sdiff_empty]
    exact finConn_of_isPreconnected hF.isPreconnected
  obtain ⟨V₀, E₀, _, hG₀, hgr₀, _⟩ := isGraph_empty.add_curve hF hfin
  rw [hzero, empty_union] at hgr₀
  obtain ⟨V, E, _, hG, hgr⟩ := exists_graph_union_finite_subarcs hp hG₀ hgr₀ J a b hcontact
  exact ⟨V, E, hG, hgr⟩

end GraphMinor.GM12
