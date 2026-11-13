module

public import GraphMinor.GM01.PathWidth
public import GraphMinor.Minor.Model
import GraphMinor.GM01.ConnectedBagIntervals
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pulling a path-decomposition through a minor model

For observation (a) on page 40 of Graph Minors I, replace each bag
by the vertices whose branches meet it. Disjoint branches inject
these vertices into the original bag. Connectivity makes their bag
indices intervals. Every represented edge has its two branches in
one bag, including a loop whose two ends lie in the same branch.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Observation (a) in the proof of GM01 (1.2), page 40, for an actual
minor model: the bags meeting its branches give the same width bound. -/
theorem HasPathWidthLE.of_minorModel {α β γ δ : Type*}
    {H : Graph α β} {G : Graph γ δ} {k : ℕ}
    {fv : α → Set γ} {fe : β → δ} (hG : HasPathWidthLE G k)
    (hH : V(H).Finite) (M : IsMinorModel H G fv fe) : HasPathWidthLE H k := by
  classical
  obtain ⟨D, hD⟩ := hG
  let bag (i : Fin D.length) : Set α := {v | v ∈ V(H) ∧ (fv v ∩ D.bag i).Nonempty}
  have hLink : ∀ e x y, H.IsLink e x y →
      ∃ a ∈ fv x, ∃ b ∈ fv y, G.IsLink (fe e) a b := by
    intro e x y he
    by_cases hxy : x = y
    · subst y
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet (M.edge_mem e he.edge_mem)
      have hall := (M.isLoopAt_iff x he.left_mem e he.edge_mem).mp he
      exact ⟨a, hall a hab.inc_left, b, hall b hab.inc_right, hab⟩
    · obtain ⟨a, ha, hae⟩ := (M.inc_iff x he.left_mem e he.edge_mem).mp he.inc_left
      obtain ⟨b, hb, hbe⟩ := (M.inc_iff y he.right_mem e he.edge_mem).mp he.inc_right
      have hab : a ≠ b := by
        intro heq
        exact Set.disjoint_left.mp (M.vertex_disjoint x he.left_mem y he.right_mem hxy)
          ha (heq.symm ▸ hb)
      have hlink := hae.isLink_other
      have hbother := hbe.eq_of_isLink_of_ne_left hlink hab.symm
      rw [← hbother] at hlink
      exact ⟨a, ha, b, hb, hlink⟩
  refine ⟨⟨D.length, bag, fun _ _ hv ↦ hv.1, ?_, ?_⟩, ?_⟩
  · intro e x y he
    obtain ⟨a, ha, b, hb, hab⟩ := hLink e x y he
    obtain ⟨i, hai, hbi⟩ := D.edge_covered (fe e) a b hab
    exact ⟨i, ⟨he.left_mem, a, ha, hai⟩, ⟨he.right_mem, b, hb, hbi⟩⟩
  · intro i j l hij hjl v hv
    obtain ⟨K, hKG, hKV, hKC⟩ := M.connected v hv.1.1
    have hi : (V(K) ∩ D.bag i).Nonempty := by
      rw [hKV]
      exact hv.1.2
    have hl : (V(K) ∩ D.bag l).Nonempty := by
      rw [hKV]
      exact hv.2.2
    have hmid := D.connected_meets_middle (hKG.trans Graph.deleteEdges_le) hKC hij hjl hi hl
    rw [hKV] at hmid
    exact ⟨hv.1.1, hmid⟩
  · intro i
    have hfin : (bag i).Finite := hH.subset (fun _ hv ↦ hv.1)
    let f : bag i → D.bag i := fun v ↦
      ⟨v.property.2.choose, v.property.2.choose_spec.2⟩
    have hf : Function.Injective f := by
      intro v w h
      apply Subtype.ext
      by_contra hvw
      have hd := M.vertex_disjoint v.val v.property.1 w.val w.property.1 hvw
      have heq : v.property.2.choose = w.property.2.choose := congrArg Subtype.val h
      exact Set.disjoint_left.mp hd v.property.2.choose_spec.1
        (heq.symm ▸ w.property.2.choose_spec.1)
    let : Finite (D.bag i) := (hD i).1.to_subtype
    have hcard := Nat.card_le_card_of_injective f hf
    change (bag i).ncard ≤ (D.bag i).ncard at hcard
    exact ⟨hfin, hcard.trans (hD i).2⟩

end GraphMinor.GM01
