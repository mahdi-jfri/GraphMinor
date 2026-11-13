module

public import GraphMinor.GM16.Section3
import GraphMinor.GM09.Section4b
import GraphMinor.GM09.Basic

/-!
# The local ring location in XVI (1.3)

For each large society, the proof on page 51 enumerates its boundary
and applies (3.2). We retain the boundary order, the separator bound,
the ring property of every torso, and the edge cover of the construction.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph GM06 GM09 GM14
universe u v

/-- The local location assigned to a large society in XVI (1.3),
page 51, obtained from the decomposition in (3.2). -/
theorem exists_society_ring_location {α : Type u} {β : Type v}
    (A : Society α β) {ρ : ℕ} (hVortex : IsRhoVortex A ρ)
    (hne : A.Ω.bar.Nonempty) :
    ∃ (t : List α) (ℒ : Set (Graph α β × Graph α β)),
      t.Nodup ∧ {x | x ∈ t} = A.Ω.bar ∧ A.Ω.IsClockwiseSeq t ∧
      IsGraphLocation A.G ℒ ∧
      (∀ p ∈ ℒ, A.Ω.bar ⊆ V(p.2)) ∧
      (∀ p ∈ ℒ, (V(p.1) ∩ V(p.2)).ncard ≤ 2 * ρ + 1) ∧
      (∀ e ∈ E(A.G), ∃ p ∈ ℒ, e ∈ E(p.1)) ∧
      (∀ H : Graph α β, IsTorsoOfDesign (graphLocationDesign A.G ℒ) H →
        IsRRing H (2 * ρ + 1) t) ∧
      (∀ x ∈ V(A.G), ∃ p ∈ ℒ, x ∈ V(p.1)) := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t, hlen, hset, _, hcw⟩ :=
    A.Ω.exists_isClockwiseSeq_of_subset_bar (Subset.refl _) hx
  have htne : 1 ≤ t.length := by
    rw [hlen]
    exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt ((ncard_pos A.Ω.finite_bar).mpr ⟨x, hx⟩))
  let f : Fin t.length → α := t.get
  have hf : Injective f := List.nodup_iff_injective_get.mp hcw.1
  have hfrange : range f = A.Ω.bar := by
    rw [← hset]
    ext y
    exact ⟨fun ⟨i, hi⟩ => hi ▸ List.get_mem t i,
      fun hy => by obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy; exact ⟨⟨i, hi⟩, rfl⟩⟩
  have hft : List.ofFn f = t := List.ofFn_get t
  obtain ⟨P, Q, hSep, hBar, _, hLoc, hOrder, hVertexCover, hCover, hRing⟩ :=
    theorem_3_2_with_edge_cover A ρ t.length f htne hVortex hf hfrange (hft.symm ▸ hcw)
  let ℒ := range (fun i => (P i, Q i))
  refine ⟨t, ℒ, hcw.1, hset, hcw, hLoc, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ y hy
    obtain ⟨j, rfl⟩ := hfrange.symm ▸ hy
    exact hBar i j
  · rintro _ ⟨i, rfl⟩
    exact hOrder i
  · intro e he
    obtain ⟨i, hei⟩ := hCover e he
    exact ⟨(P i, Q i), mem_range_self i, hei⟩
  · intro H hH
    exact hft ▸ hRing H hH

  · intro x hx
    obtain ⟨i, hxi⟩ := hVertexCover x hx
    exact ⟨(P i, Q i), mem_range_self i, hxi⟩

end GraphMinor.GM16
