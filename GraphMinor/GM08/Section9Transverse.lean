module

public import GraphMinor.GM08.Section9

/-!
# Counting vertices across the nest in VIII (9.3)

A connected set joining the two parallel rings crosses every circuit
between them. When the set is normal, each crossing is a drawing vertex.
Disjointness of the circuits makes these vertices distinct. This gives
the transverse-distance condition in Graph Minors VII (9.4).
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- A connected set from an inner disc to the boundary of an outer disc
meets each intervening nest circuit. This is the separation step in the
application of VII (9.4) in VIII (9.3), page 270. -/
theorem DrawingNest.meets_circuit_between_discs {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) {B₁ B₂ A : Set S}
    (hB₂ : IsClosedDisc B₂) (hB₂Δ : B₂ ⊆ Δ)
    {j k m : Fin s} (hjk : j ≤ m) (hmk : m < k)
    (hinner : B₁ ⊆ discInt (N.circuit j).ins)
    (houter : (N.circuit k).ins ⊆ B₂)
    (hA : IsPreconnected A) (hAΔ : A ⊆ Δ)
    (hA₁ : (A ∩ B₁).Nonempty) (hA₂ : (A ∩ discBd B₂).Nonempty) :
    (A ∩ (N.circuit m).U).Nonempty := by
  obtain ⟨x, hxA, hx₁⟩ := hA₁
  obtain ⟨y, hyA, hy₂⟩ := hA₂
  have hxint : x ∈ discInt (N.circuit m).ins :=
    (N.insideDisc_subset_of_le hΔ hjk).2 (hinner hx₁)
  have hynot : y ∉ (N.circuit m).ins := by
    intro hy
    have hyint : y ∈ discInt B₂ :=
      discInt_mono_of_closedDisc hΔ (N.circuit k).isInside.1
        (N.circuit k).isInside.2.1 houter hB₂Δ hB₂
        (N.insideDisc_subset_discInt_of_lt hΔ hmk hy)
    exact hyint.2 hy₂
  by_contra hnone
  have hdis : Disjoint A (discBd (N.circuit m).ins) := by
    rw [(N.circuit m).isInside.2.2.1]
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnone)
  rcases side_of_closedDisc hΔ (N.circuit m).isInside.1 hAΔ
      (N.circuit m).isInside.2.1 hA hdis with hin | hout
  · exact hynot (discInt_subset _ (hin hyA))
  · exact disjoint_left.mp hout hxA hxint.1

/-- A normal set meeting a family of distinct nest circuits contains at
least as many drawing vertices. Each circuit supplies a different vertex. -/
theorem DrawingNest.card_le_vertices_of_meets {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s n : ℕ} (N : DrawingNest D Δ r s) {A : Set S} (hnormal : D.IsNormal A)
    (f : Fin n → Fin s) (hf : Function.Injective f)
    (hmeet : ∀ i, (A ∩ (N.circuit (f i)).U).Nonempty) :
    n ≤ (D.V ∩ A).ncard := by
  classical
  choose x hx using hmeet
  have hxV : ∀ i, x i ∈ D.V ∩ A := fun i =>
    ⟨hnormal ⟨(hx i).1, (N.circuit (f i)).U_sub_drawing (hx i).2⟩, (hx i).1⟩
  have hinj : Function.Injective x := by
    intro i j heq
    apply hf
    by_contra hne
    exact disjoint_left.mp (N.pairwise_disjoint_circuits hΔ hne)
      (hx i).2 (heq ▸ (hx j).2)
  have hcard : (range x).ncard = n := by
    rw [ncard_range_of_injective hinj, Nat.card_fin]
  rw [← hcard]
  exact ncard_le_ncard (range_subset_iff.mpr hxV) (D.finite_V.inter_of_left A)

end GraphMinor.GM08
