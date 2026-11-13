module

public import GraphMinor.GM08.Section17RootLeaves

/-!
# Contracting the new root leaves in the target

The original graft is simulated in its root-leaf extension. Use the
old vertex together with its new leaf as a branch at each root, and
singletons at the other vertices. The new pendant edges connect the
two-point branches, and every original edge keeps its label in the
left summand. This is the target contraction used to remove collar
leaves after VII (9.3) in the proof of VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v

private theorem old_inc {α : Type u} {β : Type v} (X : Graft α β) (e : β) (a : α) :
    (rootLeafGraph X).Inc (Sum.inl e) (Sum.inl a) ↔ X.G.Inc e a := by
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | inl b => exact ⟨b, hz⟩
    | inr b => exact False.elim hz
  · rintro ⟨b, hb⟩
    exact ⟨Sum.inl b, hb⟩

private theorem not_new_inc {α : Type u} {β : Type v} (X : Graft α β) (e : β) (a : α) :
    ¬ (rootLeafGraph X).Inc (Sum.inl e) (Sum.inr a) := by
  rintro ⟨z, hz⟩
  cases z <;> exact hz

/-- The contraction branch consists of the old vertex and, at a root,
its new leaf. This is the explicit vertex map for the target contraction
in VIII (17.2). -/
@[expose] noncomputable def rootLeafContractionBranches {α : Type u} {β : Type v}
    (X : Graft α β) (a : α) : Set (α ⊕ α) := by
  classical
  exact {Sum.inl a} ∪ if a ∈ X.T then {Sum.inr a} else ∅

/-- The original graft is simulated in its root-leaf extension by
contracting each added leaf edge. This is the target contraction in
VIII (17.2), page 284. -/
theorem rootLeafContractionSimulation {α : Type u} {β : Type v} (X : Graft α β) :
    IsGraftSimulation X (rootLeafGraft X) (rootLeafContractionBranches X) Sum.inl := by
  classical
  let ηv : α → Set (α ⊕ α) := rootLeafContractionBranches X
  have hleft : ∀ a b : α, Sum.inl b ∈ ηv a ↔ b = a := by intro a b; simp [ηv, rootLeafContractionBranches]
  have hright : ∀ a b : α, Sum.inr b ∈ ηv a ↔ b = a ∧ a ∈ X.T := by
    intro a b
    by_cases ha : a ∈ X.T <;> simp [ηv, rootLeafContractionBranches, ha]
  have hVsub : ∀ a ∈ V(X.G), ηv a ⊆ V(rootLeafGraph X) := by
    intro a ha z hz
    cases z with
    | inl b => exact (inl_mem_rootLeafGraph_vertexSet X b).mpr ((hleft a b).mp hz ▸ ha)
    | inr b =>
      obtain ⟨rfl, ht⟩ := (hright a b).mp hz
      exact (inr_mem_rootLeafGraph_vertexSet X b).mpr ht
  refine ⟨?_, ?_, ?_⟩
  · refine {
      vertex_nonempty := fun a _ => ⟨Sum.inl a, (hleft a a).mpr rfl⟩
      vertex_subset := hVsub
      edge_mem := fun e he => (inl_mem_rootLeafGraph_edgeSet X e).mpr he
      vertex_disjoint := ?_
      edge_injOn := Sum.inl_injective.injOn
      inc_iff := ?_
      isLoopAt_iff := ?_
      connected := ?_ }
    · intro a ha b hb hab
      apply disjoint_left.mpr
      intro z hzA hzB
      cases z with
      | inl c => exact hab (((hleft a c).mp hzA).symm.trans ((hleft b c).mp hzB))
      | inr c => exact hab (((hright a c).mp hzA).1.symm.trans ((hright b c).mp hzB).1)
    · intro a ha e he
      constructor
      · intro h
        exact ⟨Sum.inl a, (hleft a a).mpr rfl, (old_inc X e a).mpr h⟩
      · rintro ⟨z, hz, hinc⟩
        cases z with
        | inl b =>
          have hb := (hleft a b).mp hz
          exact hb ▸ (old_inc X e b).mp hinc
        | inr b => exact False.elim (not_new_inc X e b hinc)
    · intro a ha e he
      constructor
      · intro hloop z hinc
        cases z with
        | inl b => exact (hleft a b).mpr (hloop.eq_of_inc ((old_inc X e b).mp hinc)).symm
        | inr b => exact False.elim (not_new_inc X e b hinc)
      · intro hall
        obtain ⟨b, c, hlink⟩ := X.G.exists_isLink_of_mem_edgeSet he
        have hb := (hleft a b).mp (hall (Sum.inl b) ((old_inc X e b).mpr hlink.inc_left))
        have hc := (hleft a c).mp (hall (Sum.inl c) ((old_inc X e c).mpr hlink.inc_right))
        rw [hb, hc] at hlink
        exact hlink
    · intro a ha
      let K := ((rootLeafGraph X).deleteEdges (Sum.inl '' E(X.G))).induce (ηv a)
      have hKle : K ≤ (rootLeafGraph X).deleteEdges (Sum.inl '' E(X.G)) :=
        Graph.induce_le (hVsub a ha)
      refine ⟨K, hKle, rfl, ⟨Sum.inl a, (hleft a a).mpr rfl⟩, ?_⟩
      intro z hz w hw
      change z ∈ ηv a at hz
      change w ∈ ηv a at hw
      by_cases ht : a ∈ X.T
      · have hpair : ηv a = {Sum.inl a, Sum.inr a} := by
          ext x
          simp [ηv, rootLeafContractionBranches, ht, or_comm]
        have hadj : K.Adj (Sum.inl a) (Sum.inr a) := by
          refine ⟨Sum.inr a, ⟨?_, ?_⟩, (hleft a a).mpr rfl, (hright a a).mpr ⟨rfl, ht⟩⟩
          · exact ⟨ht, rfl, rfl⟩
          · simp
        rw [hpair] at hz hw
        rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
        · exact .refl
        · exact Relation.ReflTransGen.single hadj
        · exact Relation.ReflTransGen.single hadj.symm
        · exact .refl
      · have hsingle : ηv a = {Sum.inl a} := by simp [ηv, rootLeafContractionBranches, ht]
        rw [hsingle, mem_singleton_iff] at hz hw
        subst hz hw
        exact .refl
  · exact rootLeafGraft_index X
  · intro a ha
    exact ⟨Sum.inr a, (hright a a).mpr ⟨rfl, ha⟩,
      (inr_mem_rootLeafGraft_roots X a).mpr ha⟩

/-- Contracting the added root leaf edges gives the original graft. -/
theorem isGraftSimulatedIn_rootLeafGraft {α : Type u} {β : Type v} (X : Graft α β) :
    IsGraftSimulatedIn X (rootLeafGraft X) :=
  ⟨rootLeafContractionBranches X, Sum.inl, rootLeafContractionSimulation X⟩

end GraphMinor.GM08
