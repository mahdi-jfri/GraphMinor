module

public import GraphMinor.GM08.Section9

/-!
# Keeping one more enclosed circuit in VIII (9.1)

The proof on page 270 keeps strictly interior circuits. For an even boundary
size this loses a circuit that is useful in the small sleeve case. Here we
count two intersections for every circuit that is not enclosed by the ring.
This keeps `k / 2 + 1` enclosed circuits when the ring has fewer than `k` vertices.
It follows the same separation and counting argument as (8.2).
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A circuit meeting the inside of a normal ring but not enclosed by it
meets the ring at least twice. Removing at most one point would leave a
connected set, which cannot meet both sides of the ring. -/
theorem two_le_ncard_inter_of_not_enclosed {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFn : D.IsNormal F)
    (C : DiscCircuit D Δ) (hmeet : ∃ x ∈ C.U, InsideOArc Δ F x)
    (hnot : ¬ OArcEncloses Δ F C.U) : 2 ≤ (C.U ∩ F).ncard := by
  have hfin : (C.U ∩ F).Finite := D.finite_V.subset fun x hx =>
    hFn ⟨hx.2, C.U_sub_drawing hx.1⟩
  by_contra hlt
  have hle : (C.U ∩ F).ncard ≤ 1 := by omega
  have hconn := isPreconnected_oArc_sdiff_of_ncard_le_one C.isOArc_U hfin hle
  obtain ⟨B, hB, -⟩ := disc_oArc Δ F hΔ hFΔ hFo
  have hdis : Disjoint (C.U \ F) (discBd B) := by
    rw [hB.2.2.1]
    exact disjoint_sdiff_left
  obtain ⟨x, hxC, hxF⟩ := hmeet
  have hxint := (insideOArc_iff_mem_discInt hΔ hB).mp hxF
  have hxdiff : x ∈ C.U \ F := ⟨hxC, hB.2.2.1 ▸ hxint.2⟩
  rcases side_of_closedDisc hΔ hB.1 (sdiff_subset.trans C.U_sub_disc) hB.2.1 hconn hdis
      with hin | hout
  · exact hnot fun y hy => (insideOArc_iff_mem_discInt hΔ hB).mpr (hin hy)
  · exact Set.disjoint_left.mp hout hxdiff hxint.1

/-- The enclosed version of the counting step of (8.2), used to correct the
small sleeve case in VIII (9.1), page 270. If `m < 2(s-j)`, circuit `j` is
enclosed by the ring. Otherwise all `s-j` circuits from there onwards
meet the ring at least twice, using at least `2(s-j)` distinct vertices. -/
theorem DrawingNest.circuit_enclosed_of_card_lt {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 0 < s)
    (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFn : D.IsNormal F)
    (henc : OArcEncloses Δ F (N.circuit ⟨0, hs⟩).U)
    (hcard : (D.V ∩ F).ncard < r) (j : Fin s)
    (hj : (D.V ∩ F).ncard < 2 * (s - j.val)) :
    OArcEncloses Δ F (N.circuit j).U := by
  classical
  obtain ⟨-, -, hmeet⟩ := N.exists_radialPath_inside hΔ hs hFΔ hFo hFn henc hcard
  obtain ⟨B, hB, -⟩ := disc_oArc Δ F hΔ hFΔ hFo
  by_contra hnot
  let sh : Fin (s - j.val) → Fin s := fun i => ⟨j.val + i.val, by have := i.isLt; omega⟩
  have htwo : ∀ i : Fin (s - j.val), 2 ≤ ((N.circuit (sh i)).U ∩ F).ncard := by
    intro i
    apply two_le_ncard_inter_of_not_enclosed hΔ hFΔ hFo hFn _ (hmeet (sh i))
    intro hlater
    apply hnot
    have hmono := insideDisc_subset_of_oArcEncloses hΔ hB (N.circuit (sh i)).isInside hlater
    have hle : j ≤ sh i := Fin.le_iff_val_le_val.mpr (Nat.le_add_right _ _)
    have hCsub : (N.circuit j).U ⊆ B := fun x hx =>
      hmono.1 ((N.insideDisc_subset_of_le hΔ hle).1
        (discBd_subset _ ((N.circuit j).isInside.2.2.1 ▸ hx)))
    exact (oArcEncloses_iff_subset hΔ hB).mpr hCsub
  have hfin : ∀ i : Fin (s - j.val), ((N.circuit (sh i)).U ∩ F).Finite :=
    fun i => D.finite_V.subset fun x hx => hFn ⟨hx.2, (N.circuit _).U_sub_drawing hx.1⟩
  have hex : ∀ i : Fin (s - j.val), ∃ a b,
      a ∈ (N.circuit (sh i)).U ∩ F ∧ b ∈ (N.circuit (sh i)).U ∩ F ∧ a ≠ b :=
    fun i => (Set.one_lt_ncard_iff (hfin i)).mp (by have := htwo i; omega)
  choose a b ha hb hab using hex
  let f : Fin (s - j.val) × Fin 2 → S := fun x =>
    if x.2.val = 0 then a x.1 else b x.1
  have hf : ∀ x, f x ∈ (N.circuit (sh x.1)).U ∩ F := by
    intro x
    dsimp only [f]
    split_ifs
    · exact ha _
    · exact hb _
  have hinj : Function.Injective f := by
    rintro ⟨i, ε⟩ ⟨i', ε'⟩ heq
    have hii : i = i' := by
      by_contra hne
      have hsh : sh i ≠ sh i' := by
        intro h
        have hv := congrArg Fin.val h
        exact hne (Fin.ext (Nat.add_left_cancel hv))
      exact Set.disjoint_left.mp (N.pairwise_disjoint_circuits hΔ hsh)
        (hf (i, ε)).1 (heq ▸ (hf (i', ε')).1)
    subst i'
    have heps : ε = ε' := by
      apply Fin.ext
      have hε := ε.isLt
      have hε' := ε'.isLt
      dsimp only [f] at heq
      split_ifs at heq with h0 h0'
      · omega
      · exact False.elim (hab i heq)
      · exact False.elim (hab i heq.symm)
      · omega
    exact Prod.ext rfl heps
  have hsub : range f ⊆ D.V ∩ F := by
    rintro _ ⟨x, rfl⟩
    exact ⟨hFn ⟨(hf x).2, (N.circuit _).U_sub_drawing (hf x).1⟩, (hf x).2⟩
  have hle := Set.ncard_le_ncard hsub (D.finite_V.subset inter_subset_left)
  rw [Set.ncard_range_of_injective hinj, Nat.card_prod, Nat.card_fin, Nat.card_fin] at hle
  omega

/-- The count used in the correction of VIII (9.1), page 270: a ring with fewer
than `k` vertices encloses the first `k / 2 + 1` circuits of an `(r,s)`-nest
with `r,s ≥ k`. For `k = 2` this retains both circuits rather than only one. -/
theorem DrawingNest.initial_circuits_enclosed {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) {r s k : ℕ} (N : DrawingNest D Δ r s)
    (hk : 0 < k) (hr : k ≤ r) (hs : k ≤ s)
    (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFn : D.IsNormal F)
    (henc : OArcEncloses Δ F (N.circuit ⟨0, by omega⟩).U)
    (hcard : (D.V ∩ F).ncard < k) (j : Fin (k / 2 + 1)) :
    OArcEncloses Δ F (N.circuit ⟨j.val, by have := j.isLt; omega⟩).U := by
  apply N.circuit_enclosed_of_card_lt hΔ (by omega) hFΔ hFo hFn henc
    (lt_of_lt_of_le hcard hr)
  have := j.isLt
  dsimp
  omega

/-- Arithmetic for the cycle-count obstruction in the proof of VIII (9.1).
A sleeve with `m < k` spokes and `ceil(m/2)` circuits has a smaller
cycle count than a nest with `r ≥ k` radial paths and `k / 2 + 1` circuits. -/
theorem sleeve_cycle_count_lt_nest_cycle_count {m k r : ℕ}
    (hk : 2 ≤ k) (hm : m < k) (hr : k ≤ r) :
    1 + m * ((m + 1) / 2 - 1) < 1 + r * (k / 2) := by
  have hceil : (m + 1) / 2 - 1 ≤ k / 2 := by omega
  have hpos : 0 < k / 2 := by omega
  calc
    1 + m * ((m + 1) / 2 - 1) ≤ 1 + m * (k / 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left m hceil) 1
    _ < 1 + r * (k / 2) :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le hm hr) hpos) 1

end GraphMinor.GM08
