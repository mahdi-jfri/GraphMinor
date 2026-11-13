module

public import GraphMinor.GM16.SocietyRingLocation
public import GraphMinor.GM16.SmallSocietyLocation

/-!
# Choosing the locations for all societies

The proof of XVI (1.3), page 51, applies (3.2) to the large societies
and removes each small society in one separation. We choose these local
locations together, retaining their boundary, order, and edge-cover
properties and the ring conclusion for the large societies.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The local locations and boundary lists used in the proof of
XVI (1.3), page 51, with the uniform separator bound from that proof. -/
theorem exists_society_location_choices {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)} {ρ κ : ℕ}
    (hType : IsSegregationOfType G ρ κ 𝒮) :
    ∃ (ℒ : Society α β → Set (Graph α β × Graph α β)) (t : Society α β → List α),
      ∀ A ∈ 𝒮,
        IsGraphLocation A.G (ℒ A) ∧
        (∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2)) ∧
        (∀ p ∈ ℒ A, (V(p.1) ∩ V(p.2)).ncard ≤ max 3 (2 * ρ + 1)) ∧
        (∀ e ∈ E(A.G), ∃ p ∈ ℒ A, e ∈ E(p.1)) ∧
        (A.Ω.bar.ncard ≤ 3 → ℒ A = smallSocietyLocation A) ∧
        (3 < A.Ω.bar.ncard →
          (t A).Nodup ∧ {x | x ∈ t A} = A.Ω.bar ∧ A.Ω.IsClockwiseSeq (t A) ∧
          ∀ H : Graph α β, IsTorsoOfDesign (graphLocationDesign A.G (ℒ A)) H →
            IsRRing H (2 * ρ + 1) (t A)) ∧
        (∀ x ∈ V(A.G), ∃ p ∈ ℒ A, x ∈ V(p.1)) := by
  classical
  have hex : ∀ A ∈ 𝒮, ∃ (L : Set (Graph α β × Graph α β)) (t : List α),
      IsGraphLocation A.G L ∧
      (∀ p ∈ L, A.Ω.bar ⊆ V(p.2)) ∧
      (∀ p ∈ L, (V(p.1) ∩ V(p.2)).ncard ≤ max 3 (2 * ρ + 1)) ∧
      (∀ e ∈ E(A.G), ∃ p ∈ L, e ∈ E(p.1)) ∧
      (A.Ω.bar.ncard ≤ 3 → L = smallSocietyLocation A) ∧
      (3 < A.Ω.bar.ncard →
        t.Nodup ∧ {x | x ∈ t} = A.Ω.bar ∧ A.Ω.IsClockwiseSeq t ∧
        ∀ H : Graph α β, IsTorsoOfDesign (graphLocationDesign A.G L) H →
          IsRRing H (2 * ρ + 1) t) ∧
      (∀ x ∈ V(A.G), ∃ p ∈ L, x ∈ V(p.1)) := by
    intro A hA
    by_cases hlarge : 3 < A.Ω.bar.ncard
    · have hne : A.Ω.bar.Nonempty := (ncard_pos A.Ω.finite_bar).mp (by omega)
      obtain ⟨t, L, ht, hset, hcw, hLoc, hBd, hOrd, hCover, hRing, hVertexCover⟩ :=
        exists_society_ring_location A (hType.is_rho_vortex hA hlarge) hne
      exact ⟨L, t, hLoc, hBd, fun p hp => (hOrd p hp).trans (le_max_right _ _),
        hCover, fun hsmall => (not_lt_of_ge hsmall hlarge).elim,
        fun _ => ⟨ht, hset, hcw, hRing⟩, hVertexCover⟩
    · have hsmall : A.Ω.bar.ncard ≤ 3 := Nat.le_of_not_gt hlarge
      refine ⟨smallSocietyLocation A, [], smallSocietyLocation_isLocation A, ?_, ?_, ?_,
        fun _ => rfl, fun hgt => (hlarge hgt).elim, ?_⟩
      · rintro p (rfl : p = _)
        exact Subset.refl _
      · rintro p (rfl : p = _)
        change (V(A.G) ∩ A.Ω.bar).ncard ≤ _
        rw [inter_eq_self_of_subset_right A.bar_subset]
        exact hsmall.trans (le_max_left _ _)
      · intro e he
        exact ⟨(A.G, societyBoundaryGraph A), mem_singleton _, he⟩
      · intro x hx
        exact ⟨(A.G, societyBoundaryGraph A), mem_singleton _, hx⟩
  choose L t hSpec using hex
  let ℒ : Society α β → Set (Graph α β × Graph α β) :=
    fun A => if hA : A ∈ 𝒮 then L A hA else ∅
  let ts : Society α β → List α := fun A => if hA : A ∈ 𝒮 then t A hA else []
  refine ⟨ℒ, ts, ?_⟩
  intro A hA
  simpa only [ℒ, ts, dite_eq_left hA] using hSpec A hA

end GraphMinor.GM16
