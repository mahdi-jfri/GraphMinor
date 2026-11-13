module

public import GraphMinor.GM08.Section15Bridge
public import GraphMinor.GM08.Section15Assembly

/-!
# Graph Minors VIII, printed (15.1): Lemma 3 for strong tubes

This file states Lemma 3 of the proof of the printed (15.1) in `Section15PrintedFinal.lean` in the
form the assembly uses. In a tube where every normal hoop
carries at least `r` vertices, the chain of `Tube.exists_chain_decomposition` gives a
path-decomposition into tubular grafts of printed width `≥ r + 1`. Its first and last junctions are
the vertex sets of the two ends, its inner junctions have exactly `r` vertices, and any two of its
junctions are joined by `r` disjoint paths (Lemma 1, `Tube.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- Lemma 1 for a framing: if every normal hoop between two laminar normal hoops `H₁`, `H₂`
carries at least `r` vertices, then the graft has `r` disjoint paths between the vertex sets of
`H₁` and `H₂`. -/
theorem Tube.Framing.hasDisjointGraphPaths_of_forall_hoop {τ : Tube S} {X : Graft α β}
    (fr : τ.Framing X) {r : ℕ} {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween H₁ H₂ →
      r ≤ (H ∩ τ.Γ.V).ncard) :
    HasDisjointGraphPathsFromTo X.G (fr.vertsIn H₁) (fr.vertsIn H₂) r := by
  have hp := τ.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge hlam hN₁ hN₂
    fun H hH hN hsub => by rw [inter_comm]; exact hmin H hH hN hsub
  refine hasDisjointGraphPathsFromTo_of_iso_drawing fr.iso inter_subset_left ?_ ?_ hp
  · intro z hz
    refine ⟨(fr.iso.vertexEquiv.symm z).2, ?_⟩
    rw [Subtype.coe_eta, fr.iso.vertexEquiv.apply_symm_apply z]
    exact hz.2
  · intro z hz
    refine ⟨(fr.iso.vertexEquiv.symm z).2, ?_⟩
    rw [Subtype.coe_eta, fr.iso.vertexEquiv.apply_symm_apply z]
    exact hz.2

/-- **Lemma 3, in the form the assembly uses.** Let every normal hoop of a tube carry at least
`r` vertices. Then a graft framed by it has a path-decomposition into tubular grafts of printed
width `≥ r + 1` whose first and last junctions are the vertex sets of the ends, whose inner
junctions have `r` vertices, and any two of whose junctions are joined by `r` disjoint paths.

The index bound needs the two ends to carry at most `k + r` vertices: a piece has at most two
junctions, and an inner junction has `r` vertices. -/
theorem Tube.exists_strong_decomposition (σ : Tube S) {Y : Graft α β} (fr : σ.Framing Y)
    {r k : ℕ}
    (hmin : ∀ F : Set S, IsHoop F → σ.Γ.IsNormal F → F ⊆ cylinderBetween σ.F₁ σ.F₂ →
      r ≤ (F ∩ σ.Γ.V).ncard)
    (hk₁ : (fr.vertsIn σ.F₁).ncard ≤ k + r) (hk₂ : (fr.vertsIn σ.F₂).ncard ≤ k + r)
    (hkT : Y.index ≤ k + 2 * r) :
    ∃ D : GraftPathDecomposition (printedTubularClass (r + 1) (k + 2 * r)) Y,
      D.Yn 0 = fr.vertsIn σ.F₁ ∧ D.Yn D.r = fr.vertsIn σ.F₂ ∧
      (∀ i, 1 ≤ i → i < D.r → (D.Yn i).ncard = r) ∧
      (∀ i j, i < j → j ≤ D.r → HasDisjointGraphPathsFromTo Y.G (D.Yn i) (D.Yn j) r) := by
  have : T2Space S := σ.t2Space
  have hw : (r : ℕ∞) ≤ σ.width :=
    σ.le_width_iff.mpr fun F hF hN hsub => Or.inr (by exact_mod_cast hmin F hF hN hsub)
  obtain ⟨D, H, hH0, hHr, hH, hlam, hY, hint⟩ :=
    σ.exists_chain_decomposition fr (k := Y.index) le_rfl hw
  have hT : Y.T = D.Yn 0 ∪ D.Yn D.r := D.T_eq'
  have hmem : ∀ i < D.r, ∀ h hf, Graft.mk (D.Gn i) (D.Yn i ∪ D.Yn (i + 1)) h hf ∈
      printedTubularClass (r + 1) (k + 2 * r) := by
    intro i hi h hf
    obtain ⟨htub, hwid, -⟩ := tubularClass_subset_printedTubularClass _ _
      (σ.subFramedClass_subset_tubularClass _ _ (D.mem_𝒜' hi h hf))
    refine ⟨htub, hwid, ?_⟩
    change (D.Yn i ∪ D.Yn (i + 1)).ncard ≤ k + 2 * r
    have hcard : ∀ j, j ≤ D.r → (D.Yn j).ncard ≤ k + r := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [hY 0 (Nat.zero_le _), hH0]
        exact hk₁
      rcases eq_or_lt_of_le hj with rfl | hlt
      · rw [hY _ le_rfl, hHr]
        exact hk₂
      · rw [(hint j hj0 hlt).1]
        omega
    rcases Nat.lt_or_ge (i + 1) D.r with h1 | h1
    · have := (hint (i + 1) (by omega) h1).1
      have := hcard i (by omega)
      linarith [ncard_union_le (D.Yn i) (D.Yn (i + 1))]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : D.r = 1 := by omega
      rw [show 0 + 1 = D.r by omega, ← hT]
      exact hkT
    · have := (hint i hi0 hi).1
      have := hcard (i + 1) (by omega)
      linarith [ncard_union_le (D.Yn i) (D.Yn (i + 1))]
  refine ⟨D.recast hmem, ?_, ?_, ?_, ?_⟩
  · rw [GraftPathDecomposition.recast_Yn (Nat.zero_le _), hY 0 (Nat.zero_le _), hH0]
  · rw [GraftPathDecomposition.recast_r, GraftPathDecomposition.recast_Yn le_rfl, hY _ le_rfl,
      hHr]
  · intro i h1 h2
    rw [GraftPathDecomposition.recast_r] at h2
    rw [GraftPathDecomposition.recast_Yn h2.le]
    exact (hint i h1 h2).1
  · intro i j hij hj
    rw [GraftPathDecomposition.recast_r] at hj
    rw [GraftPathDecomposition.recast_Yn (by omega), GraftPathDecomposition.recast_Yn hj,
      hY i (by omega), hY j hj]
    obtain ⟨-, hNi, hsi⟩ := hH i (by omega)
    obtain ⟨-, hNj, hsj⟩ := hH j hj
    have hl := hlam i j hij hj
    refine fr.hasDisjointGraphPaths_of_forall_hoop hl hNi hNj fun F hF hN hsub => ?_
    exact hmin F hF hN (hsub.trans (cylinderBetween_subset_cylinderBetween σ.laminar hl hsi hsj))

end GraphMinor.GM08
