module

public import GraphMinor.GM08.Section9
import GraphMinor.GM08.Section9Rings
import GraphMinor.GM08.Section9Transverse

/-!
# The distance between the parallel rings in VIII (9.3)

Choose the first parallel ring after the first circuit and the second
one after the last of a prescribed number of intermediate circuits.
Every normal connected transversal contains a different drawing vertex
on each intermediate circuit. This supplies the distance condition of
Graph Minors VII (9.4).
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Parallel rings separated by `n` nest circuits have normal transverse
distance at least `n`. This verifies the distance part of VII (9.4) in
the proof of VIII (9.3), page 270. -/
theorem DrawingNest.exists_parallel_discs_with_distance {S : Type u}
    [TopologicalSpace S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s n : ℕ} (N : DrawingNest D Δ r s) (hs : n + 3 ≤ s) :
    ∃ B₁ B₂ : Set S, IsClosedDisc B₁ ∧ IsClosedDisc B₂ ∧
      (N.circuit ⟨0, by omega⟩).ins ⊆ B₁ ∧
      B₁ ⊆ discInt (N.circuit ⟨1, by omega⟩).ins ∧
      (N.circuit ⟨n + 1, by omega⟩).ins ⊆ B₂ ∧
      B₂ ⊆ discInt (N.circuit ⟨n + 2, by omega⟩).ins ∧
      D.IsNormal (discBd B₁) ∧ D.IsNormal (discBd B₂) ∧
      B₁ ⊆ discInt B₂ ∧ Disjoint (discBd B₁) (discBd B₂) ∧
      Disjoint B₂ (discBd Δ) ∧
      ∀ A : Set S, D.IsNormal A → IsPreconnected A → A ⊆ Δ →
        (A ∩ discBd B₁).Nonempty → (A ∩ discBd B₂).Nonempty →
        n ≤ (D.V ∩ A).ncard := by
  obtain ⟨B₁, B₂, hB₁, hB₂, hi, hj, hk, hl, hn₁, hn₂, hin, hd, hbd⟩ :=
    N.exists_two_parallel_discs hΔ
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (k := ⟨n + 1, by omega⟩) (l := ⟨n + 2, by omega⟩)
      (by simp) (by simp) (by simp)
  refine ⟨B₁, B₂, hB₁, hB₂, hi, hj, hk, hl, hn₁, hn₂, hin, hd, hbd, ?_⟩
  intro A hn hA hAΔ hA₁ hA₂
  let f : Fin n → Fin s := fun i => ⟨i.val + 1, by have := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j heq
    apply Fin.ext
    have he := congrArg Fin.val heq
    change i.val + 1 = j.val + 1 at he
    omega
  apply N.card_le_vertices_of_meets hΔ hn f hf
  intro i
  exact N.meets_circuit_between_discs hΔ hB₂
    (hl.trans ((discInt_subset _).trans (N.circuit _).isInside.1))
    (j := ⟨1, by omega⟩) (k := ⟨n + 1, by omega⟩)
    (by change 1 ≤ i.val + 1; omega)
    (by change i.val + 1 < n + 1; have := i.isLt; omega)
    hj hk hA hAΔ (hA₁.mono (inter_subset_inter_right A (discBd_subset B₁))) hA₂

end GraphMinor.GM08
