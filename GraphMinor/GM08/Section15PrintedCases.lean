module

public import GraphMinor.GM08.Section15PrintedTrain

/-!
# Graph Minors VIII, printed (15.1): the left and right parts

From the hoops that Lemma 4 gives, this file builds the left part of the train
(`Tube.Framing.left_part₁` for one pocket, `Tube.Framing.left_part₂` for two pockets) and the right
part (`Tube.Framing.right_part`, Lemma 4 at the second end, read in the tube with its ends
exchanged).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

namespace Tube.Framing

variable {τ : Tube S} {X : Graft α β}

/-- **The left part with one pocket.** Let Lemma 4, applied between `F₁` and a hoop `Rb`, give the
far side `L'` of the pocket and the hoop `L` through one more vertex, and let `L` carry `r`
vertices. Then the part before `L` decomposes from `F₁` to `L`, with all later junctions the
vertices of `L`. -/
theorem left_part₁ (fr : τ.Framing X) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {Rb L' L : Set S} {v : S} (hRb : IsHoop Rb) (hRbsub : Rb ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hL' : IsHoop L') (hNL' : τ.Γ.IsNormal L') (hL'sub : L' ⊆ cylinderBetween τ.F₁ Rb)
    (hL'V : L' ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V) (hL : IsHoop L) (hNL : τ.Γ.IsNormal L)
    (hLsub : L ⊆ cylinderBetween L' Rb) (hLV : L ∩ τ.Γ.V = insert v (L' ∩ τ.Γ.V))
    (hcov : τ.Γ.U ∩ cylinderBetween L' Rb ⊆ cylinderBetween L Rb) {r k : ℕ}
    (hr : (L ∩ τ.Γ.V).ncard = r) :
    cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hL ∧
      cap.disc₁ τ.isCylinder.1 hL ⊆ cap.disc₁ τ.isCylinder.1 hRb ∧
      Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
        (fr.vertsIn (cylinderBetween τ.F₁ L)) (fr.edgesIn (cylinderBetween τ.F₁ L))
        (fr.vertsIn τ.F₁) (fr.vertsIn L) (fr.vertsIn L) (fr.vertsIn L) r := by
  have hS := τ.isCylinder
  have hRb12 := (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hRb hle).mp hRbsub
  have o1 := (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ hRb hL' hRb12.1).mp hL'sub
  have o2 := (cap.hoop_subset_cylinderBetween_iff hS hL' hRb hL o1.2).mp hLsub
  have hstrip := τ.strip_of_cover cap hL' hL hRb o2.1 o2.2 hcov
  have hpocket : fr.vertsIn τ.F₁ = fr.vertsIn L' := fr.vertsIn_eq_of_inter_eq hL'V.symm
  have hAJ : fr.vertsIn τ.F₁ ⊆ fr.vertsIn L :=
    fr.vertsIn_subset_of_inter_subset (by rw [hLV, hL'V]; exact subset_insert _ _)
  have hJr : (fr.vertsIn L).ncard = r := by rw [fr.ncard_vertsIn]; exact hr
  have h0 := fr.decomposes_base cap τ.isNormal_F₁ (fr.vertsIn_subset_V L) hAJ hAJ
    (t := r + 1) (u := k + 2 * r) (by rw [hJr]) (by rw [hJr]; omega) r
  have h1 := fr.left_step cap τ.isHoop_F₁ hL' hL hL τ.isNormal_F₁ hNL' hNL subset_rfl o1.1 o2.1
    subset_rfl (o2.2.trans hRb12.2) hpocket hstrip hAJ subset_rfl le_rfl (by omega) hJr h0
  have hlam := (cap.areLaminarHoops_iff hS τ.isHoop_F₁ hL).mpr (.inl (o1.1.trans o2.1))
  exact ⟨o1.1.trans o2.1, o2.2, h1.congr_sets
    (union_eq_left.mpr (fr.vertsIn_mono (subset_cylinderBetween_right hlam))) rfl⟩

/-- **The left part with two pockets.** As `left_part₁`, when Lemma 4 is applied twice: first
between `F₁` and `Rb`, giving `L₁'`, `L₁`, and then between `L₁` and `Rb`, giving `L₂'`, `L₂`. The
bridges of both pockets are padded by the vertices of `L₂`. -/
theorem left_part₂ (fr : τ.Framing X) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {Rb L₁' L₁ L₂' L₂ : Set S} {v₁ v₂ : S} (hRb : IsHoop Rb)
    (hRbsub : Rb ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hL₁' : IsHoop L₁') (hNL₁' : τ.Γ.IsNormal L₁') (hL₁'sub : L₁' ⊆ cylinderBetween τ.F₁ Rb)
    (hL₁'V : L₁' ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V) (hL₁ : IsHoop L₁) (hNL₁ : τ.Γ.IsNormal L₁)
    (hL₁sub : L₁ ⊆ cylinderBetween L₁' Rb) (hL₁V : L₁ ∩ τ.Γ.V = insert v₁ (L₁' ∩ τ.Γ.V))
    (hcov₁ : τ.Γ.U ∩ cylinderBetween L₁' Rb ⊆ cylinderBetween L₁ Rb)
    (hL₂' : IsHoop L₂') (hNL₂' : τ.Γ.IsNormal L₂') (hL₂'sub : L₂' ⊆ cylinderBetween L₁ Rb)
    (hL₂'V : L₂' ∩ τ.Γ.V = L₁ ∩ τ.Γ.V) (hL₂ : IsHoop L₂) (hNL₂ : τ.Γ.IsNormal L₂)
    (hL₂sub : L₂ ⊆ cylinderBetween L₂' Rb) (hL₂V : L₂ ∩ τ.Γ.V = insert v₂ (L₂' ∩ τ.Γ.V))
    (hcov₂ : τ.Γ.U ∩ cylinderBetween L₂' Rb ⊆ cylinderBetween L₂ Rb) {r k : ℕ}
    (hr : (L₂ ∩ τ.Γ.V).ncard = r) :
    cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hL₂ ∧
      cap.disc₁ τ.isCylinder.1 hL₂ ⊆ cap.disc₁ τ.isCylinder.1 hRb ∧
      Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
        (fr.vertsIn (cylinderBetween τ.F₁ L₂)) (fr.edgesIn (cylinderBetween τ.F₁ L₂))
        (fr.vertsIn τ.F₁) (fr.vertsIn L₂) (fr.vertsIn L₂) (fr.vertsIn L₂) r := by
  have hS := τ.isCylinder
  have hRb12 := (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hRb hle).mp hRbsub
  have o1 := (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ hRb hL₁' hRb12.1).mp hL₁'sub
  have o2 := (cap.hoop_subset_cylinderBetween_iff hS hL₁' hRb hL₁ o1.2).mp hL₁sub
  have o3 := (cap.hoop_subset_cylinderBetween_iff hS hL₁ hRb hL₂' o2.2).mp hL₂'sub
  have o4 := (cap.hoop_subset_cylinderBetween_iff hS hL₂' hRb hL₂ o3.2).mp hL₂sub
  have hstrip₁ := τ.strip_of_cover cap hL₁' hL₁ hRb o2.1 o2.2 hcov₁
  have hstrip₂ := τ.strip_of_cover cap hL₂' hL₂ hRb o4.1 o4.2 hcov₂
  have hpocket₁ : fr.vertsIn τ.F₁ = fr.vertsIn L₁' := fr.vertsIn_eq_of_inter_eq hL₁'V.symm
  have hpocket₂ : fr.vertsIn L₁ = fr.vertsIn L₂' := fr.vertsIn_eq_of_inter_eq hL₂'V.symm
  have hBJ : fr.vertsIn L₁ ⊆ fr.vertsIn L₂ :=
    fr.vertsIn_subset_of_inter_subset (by rw [hL₂V, hL₂'V]; exact subset_insert _ _)
  have hAB : fr.vertsIn τ.F₁ ⊆ fr.vertsIn L₁ :=
    fr.vertsIn_subset_of_inter_subset (by rw [hL₁V, hL₁'V]; exact subset_insert _ _)
  have hJr : (fr.vertsIn L₂).ncard = r := by rw [fr.ncard_vertsIn]; exact hr
  have hL₂F₂ := o4.2.trans hRb12.2
  have h0 := fr.decomposes_base cap τ.isNormal_F₁ (fr.vertsIn_subset_V L₂) (hAB.trans hBJ)
    (hAB.trans hBJ) (t := r + 1) (u := k + 2 * r) (by rw [hJr]) (by rw [hJr]; omega) r
  have h1 := fr.left_step cap τ.isHoop_F₁ hL₁' hL₁ hL₂ τ.isNormal_F₁ hNL₁' hNL₁ subset_rfl o1.1
    o2.1 (o3.1.trans o4.1) hL₂F₂ hpocket₁ hstrip₁ (hAB.trans hBJ) hBJ le_rfl (by omega) hJr h0
  have h2 := fr.left_step cap hL₁ hL₂' hL₂ hL₂ hNL₁ hNL₂' hNL₂ (o1.1.trans o2.1) o3.1 o4.1
    subset_rfl hL₂F₂ hpocket₂ hstrip₂ hBJ subset_rfl le_rfl (by omega) hJr h1
  have hlam := (cap.areLaminarHoops_iff hS τ.isHoop_F₁ hL₂).mpr
    (.inl (o1.1.trans (o2.1.trans (o3.1.trans o4.1))))
  exact ⟨o1.1.trans (o2.1.trans (o3.1.trans o4.1)), o4.2, h2.congr_sets
    (union_eq_left.mpr (fr.vertsIn_mono (subset_cylinderBetween_right hlam))) rfl⟩

/-- The framing of `X` by the tube with its two ends exchanged. -/
def swap (fr : τ.Framing X) : τ.swap.Framing X where
  iso := fr.iso
  mem_F_iff v := by
    change (fr.iso.vertexEquiv v).1 ∈ τ.F₂ ∪ τ.F₁ ↔ v.1 ∈ X.T
    rw [union_comm]
    exact fr.mem_F_iff v

/-- **The right part.** Lemma 4 at the second end `B`, between a hoop `H₀` and `F₂`, gives a hoop
`R` through the vertices of `B` and one more vertex `w`, such that no normal hoop between `H₀`
and `R` carries exactly the vertices of `B`. When `R` carries `r` vertices, the part after `R`
decomposes from `R` to `F₂`, with all earlier junctions the vertices of `R`. -/
theorem right_part (fr : τ.Framing X) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    {H₀ : Set S} (hH₀ : IsHoop H₀) (hN₀ : τ.Γ.IsNormal H₀)
    (hH₀sub : H₀ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween H₀ τ.F₂ →
      (τ.F₂ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard)
    (hBA : ∃ x ∈ H₀ ∩ τ.Γ.V, x ∉ τ.F₂) {r k : ℕ} :
    ∃ R : Set S, ∃ hR : IsHoop R, τ.Γ.IsNormal R ∧
      cap.disc₁ τ.isCylinder.1 hH₀ ⊆ cap.disc₁ τ.isCylinder.1 hR ∧
      cap.disc₁ τ.isCylinder.1 hR ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ ∧
      ∃ w ∈ τ.Γ.V, w ∉ τ.F₂ ∧ R ∩ τ.Γ.V = insert w (τ.F₂ ∩ τ.Γ.V) ∧
      (∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween H₀ R →
        F ∩ τ.Γ.V ≠ τ.F₂ ∩ τ.Γ.V) ∧
      ((R ∩ τ.Γ.V).ncard = r → Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
        (fr.vertsIn (cylinderBetween R τ.F₂)) (fr.edgesIn (cylinderBetween R τ.F₂))
        (fr.vertsIn R) (fr.vertsIn R) (fr.vertsIn R) (fr.vertsIn τ.F₂) r) := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hlam : AreLaminarHoops τ.F₂ H₀ :=
    (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH₀ hH₀sub).2.symm
  obtain ⟨R', hR', hNR', hR'sub, hR'V, w, hwV, hwR', R, hR, hNR, hRsub, hRV, hcov, hne⟩ :=
    τ.swap.lemma4_sub (H₁ := τ.F₂) (H₂ := H₀) hlam τ.isNormal_F₂ hN₀
      (fun F hF hN hsub => hmin F hF hN (by rwa [cylinderBetween_comm] at hsub)) hBA
  have hH₀o := (cap.hoop_subset_cylinderBetween_iff hS τ.isHoop_F₁ τ.isHoop_F₂ hH₀ hle).mp hH₀sub
  have o1 := (cap.hoop_subset_cylinderBetween_iff hS hH₀ τ.isHoop_F₂ hR' hH₀o.2).mp
    (by rwa [cylinderBetween_comm] at hR'sub)
  have o2 := (cap.hoop_subset_cylinderBetween_iff hS hH₀ hR' hR o1.1).mp
    (by rwa [cylinderBetween_comm] at hRsub)
  have hwF₂ : w ∉ τ.F₂ := fun h => hwR' ((hR'V ▸ ⟨h, hwV⟩ : w ∈ R' ∩ τ.Γ.V).1)
  refine ⟨R, hR, hNR, o2.1, o2.2.trans o1.2, w, hwV, hwF₂,
    by change R ∩ τ.swap.Γ.V = insert w (τ.swap.F₁ ∩ τ.swap.Γ.V); rw [hRV, hR'V]; rfl,
    fun F hF hN hsub => ?_,
    fun hr => ?_⟩
  · exact hne F hF hN (by rwa [cylinderBetween_comm] at hsub)
  · obtain ⟨cap', hle'⟩ := CylinderSphereCap.exists_oriented τ.swap.isCylinder τ.swap.isHoop_F₁
      τ.swap.isHoop_F₂ τ.swap.laminar
    obtain ⟨-, -, hpart⟩ := fr.swap.left_part₁ cap' hle' (Rb := H₀) (k := k) hH₀
      (by change H₀ ⊆ cylinderBetween τ.F₂ τ.F₁; rwa [cylinderBetween_comm]) hR' hNR' hR'sub hR'V
      hR hNR hRsub hRV hcov hr
    have h : Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
        (fr.vertsIn (cylinderBetween τ.F₂ R)) (fr.edgesIn (cylinderBetween τ.F₂ R))
        (fr.vertsIn τ.F₂) (fr.vertsIn R) (fr.vertsIn R) (fr.vertsIn R) r := hpart
    rw [cylinderBetween_comm] at h
    exact h.reverse

end Tube.Framing

end GraphMinor.GM08
