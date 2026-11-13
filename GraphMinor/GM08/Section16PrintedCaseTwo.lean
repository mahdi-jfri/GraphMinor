module

public import GraphMinor.GM08.Section16Minimal
public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section16PrintedStep
import GraphMinor.GM08.Section16Step

/-!
# The boundary-linking contradiction with the printed width

Graph Minors VIII (16.2), page 283, chooses a closest small hoop and supposes
that the first piece contains a long, wide tube. Moving one of its boundary
hoops inward gives a new vertex before the chosen small hoop. Minimality and
Menger then give all the paths required for boundary linking. If moving the
hoop loses printed width, use the old-boundary-exception hoop supplied by
`exists_printed_wide_hoop_after_step` instead, with its proved length bound.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- The contradiction in Case 2 of VIII (16.2), page 283, for inner hoops
ordered along the cylinder. All assumptions describe the chosen small hoop,
the minimum cut size, and the proposed inner tube. -/
theorem Tube.printedBoundaryLinked_of_long_tube_before_closest {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (cap : CylinderSphereCap S) {r s m : ℕ}
    (hpositive : 0 < (τ.Γ.V ∩ τ.F₁).ncard)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (hcount : (τ.Γ.V ∩ τ.F₂).ncard = m)
    (hglobal : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
      H ⊆ cylinderBetween τ.F₁ τ.F₂ → m ≤ (τ.Γ.V ∩ H).ncard)
    {F A B : Set S} (hF : IsHoop F) (hA : IsHoop A) (hB : IsHoop B)
    (hFsub : F ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₁).ncard →
      (τ.firstSideVertices F).ncard ≤ (τ.firstSideVertices H).ncard)
    (h₁B : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hB)
    (hBA : cap.disc₁ τ.isCylinder.1 hB ⊆ cap.disc₁ τ.isCylinder.1 hA)
    (hAF : cap.disc₁ τ.isCylinder.1 hA ⊆ cap.disc₁ τ.isCylinder.1 hF)
    (hNA : τ.Γ.IsNormal A) (hNB : τ.Γ.IsNormal B)
    (hw : (r : ℕ∞) ≤ (τ.subTube
      ((cap.areLaminarHoops_iff τ.isCylinder hA hB).mpr (Or.inr hBA)) hNA hNB).printedWidth)
    (hl : s + 2 ≤ (τ.subTube
      ((cap.areLaminarHoops_iff τ.isCylinder hA hB).mpr (Or.inr hBA)) hNA hNB).length) :
    τ.IsPrintedBoundaryLinked r s := by
  have : T2Space S := τ.t2Space
  let hab := (cap.areLaminarHoops_iff τ.isCylinder hA hB).mpr (Or.inr hBA)
  let σ := τ.subTube hab hNA hNB
  have hFpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hF hle).mp hFsub
  have hAsub : A ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hA hle).mpr
      ⟨h₁B.trans hBA, hAF.trans hFpos.2⟩
  have hBsub : B ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hB hle).mpr
      ⟨h₁B, hBA.trans (hAF.trans hFpos.2)⟩
  obtain ⟨K, hKB, hNK', hKsub, ⟨v, hvV', hvK, hvA⟩, hlen⟩ := σ.exists_hoop_step_inward hl
  have hK : IsHoop K := hKB.2.1
  have hKsubBA : K ⊆ cylinderBetween B A := by
    simpa only [σ, Tube.subTube, cylinderBetween_comm A B] using hKsub
  have hKpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hB hA hK hBA).mp hKsubBA
  have hNK : τ.Γ.IsNormal K := (τ.subTube_isNormal_iff hab hNA hNB hKsub).mp hNK'
  have hKsubF : K ⊆ cylinderBetween τ.F₁ F :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hF hK hFpos.1).mpr
      ⟨h₁B.trans hKpos.1, hKpos.2.trans hAF⟩
  have hKall : K ⊆ cylinderBetween τ.F₁ τ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hK hle).mpr
      ⟨h₁B.trans hKpos.1, hKpos.2.trans (hAF.trans hFpos.2)⟩
  have hVeq : σ.Γ.V = τ.Γ.V ∩ cylinderBetween A B :=
    interSet_V_of_isClosed τ.Γ (isClosed_cylinderBetween hab)
  have hvV : v ∈ τ.Γ.V := (hVeq.subset hvV').1
  have hvF : v ∉ F := by
    intro hvF
    have hAF' := (cap.areLaminarHoops_iff τ.isCylinder hA hF).mpr (Or.inl hAF)
    have hKsubA : K ⊆ cylinderBetween τ.F₁ A :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hA hK
        (h₁B.trans hBA)).mpr ⟨h₁B.trans hKpos.1, hKpos.2⟩
    apply hvA
    change v ∈ A
    rw [← cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hA hF (h₁B.trans hBA) hAF]
    exact ⟨hKsubA hvK, subset_cylinderBetween_right hAF' hvF⟩
  have hfirst := τ.hoop_ncard_ge_of_closest hF hK hFsub hKsubF hmin hvV hvK hvF
  have hBinner : B ⊆ cylinderBetween A B := subset_cylinderBetween_right hab
  have hbefore : ∀ H : Set S, IsHoop H → H ⊆ cylinderBetween K B →
      H ⊆ cylinderBetween τ.F₁ K := by
    intro H hH hHsub
    have hHpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hB hK hH
      hKpos.1).mp (cylinderBetween_comm K B ▸ hHsub)
    exact (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hK hH
      (h₁B.trans hKpos.1)).mpr ⟨h₁B.trans hHpos.1, hHpos.2⟩
  have hpos : ∀ H : Set S, IsHoop H → σ.Γ.IsNormal H → H ⊆ cylinderBetween K B →
      0 < (H ∩ σ.Γ.V).ncard := by
    intro H hH hNHσ hHsub
    have hHσsub := hHsub.trans
      (cylinderBetween_subset_cylinderBetween hab hKB hKsub hBinner)
    have hNHτ := (τ.subTube_isNormal_iff hab hNA hNB hHσsub).mp hNHσ
    have hbound := hfirst H hH hNHτ (hbefore H hH hHsub)
    have hverts : H ∩ σ.Γ.V = H ∩ τ.Γ.V := by
      rw [hVeq]
      ext x
      exact ⟨fun ⟨hxH, hxV, _⟩ => ⟨hxH, hxV⟩,
        fun ⟨hxH, hxV⟩ => ⟨hxH, hxV, hHσsub hxH⟩⟩
    rw [hverts, inter_comm H τ.Γ.V]
    exact lt_of_lt_of_le hpositive hbound
  obtain ⟨L, hLB, hNLσ, hLsub, hwidthσ, hlengthσ⟩ :=
    σ.exists_printed_wide_hoop_after_step hw hl hK hNK' hKsub hlen hpos
  have hL : IsHoop L := hLB.2.1
  have hLσsub := hLsub.trans
    (cylinderBetween_subset_cylinderBetween hab hKB hKsub hBinner)
  have hNL : τ.Γ.IsNormal L := (τ.subTube_isNormal_iff hab hNA hNB hLσsub).mp hNLσ
  have hLall := hLσsub.trans
    (cylinderBetween_subset_cylinderBetween τ.laminar hab hAsub hBsub)
  have hLfirst := hbefore L hL hLsub
  have hleftK := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hK hKall).1
  have hleftL := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hL hLall).1
  have hpaths₁ := τ.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge
    hleftL τ.isNormal_F₁ hNL (by
      intro H hH hNH hHsub
      exact hfirst H hH hNH (hHsub.trans (cylinderBetween_subset_cylinderBetween
        hleftK hleftL (subset_cylinderBetween_left hleftK) hLfirst)))
  have hright := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hB hBsub).2.symm
  have hpaths₂ : HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₂) (τ.Γ.V ∩ B)
      (τ.Γ.V ∩ τ.F₂).ncard := by
    rw [hcount]
    apply τ.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge hright τ.isNormal_F₂ hNB
    intro H hH hNH hHsub
    exact hglobal H hH hNH (hHsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar
      hright (subset_cylinderBetween_right τ.laminar) hBsub))
  have heq : σ.subTube hLB hNLσ σ.isNormal_F₂ = τ.subTube hLB hNL hNB :=
    τ.subTube_subTube hab hNA hNB hLB hLσsub hBinner hNLσ σ.isNormal_F₂
  have hwidth : (r : ℕ∞) ≤ (τ.subTube hLB hNL hNB).printedWidth := by
    rw [← heq]
    exact hwidthσ
  have hlength : s ≤ (τ.subTube hLB hNL hNB).length := by
    rw [← heq]
    exact hlengthσ
  have hLpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hB hK hL
    hKpos.1).mp (cylinderBetween_comm K B ▸ hLsub)
  have horder₁ : B ⊆ cylinderBetween τ.F₁ L :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hL hB
      (h₁B.trans hLpos.1)).mpr ⟨h₁B, hLpos.1⟩
  have horder₂ : L ⊆ cylinderBetween τ.F₂ B := by
    rw [cylinderBetween_comm]
    exact (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hB τ.isHoop_F₂ hL
      (hBA.trans (hAF.trans hFpos.2))).mpr
        ⟨hLpos.1, hLpos.2.trans (hKpos.2.trans (hAF.trans hFpos.2))⟩
  exact ⟨L, B, hLB, hLall, hBsub, hNL, hNB, horder₁, horder₂,
    hwidth, hlength, hpaths₁, hpaths₂⟩

/-- The first piece at the closest small hoop has no tube of width at least
`r` and length at least `s + 2`, in Case 2 of VIII (16.2), page 283. -/
theorem Tube.hasNoPrintedSubTubeOf_left_of_closest {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r s m : ℕ} {F : Set S} (hF : IsHoop F) (hNF : τ.Γ.IsNormal F)
    (hFsub : F ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hpositive : 0 < (τ.Γ.V ∩ τ.F₁).ncard)
    (hcount : (τ.Γ.V ∩ τ.F₂).ncard = m)
    (hglobal : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
      H ⊆ cylinderBetween τ.F₁ τ.F₂ → m ≤ (τ.Γ.V ∩ H).ncard)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₁).ncard →
      (τ.firstSideVertices F).ncard ≤ (τ.firstSideVertices H).ncard)
    (hnot : ¬ τ.IsPrintedBoundaryLinked r s) :
    (τ.subTube (areLaminarHoops_of_subset_cylinderBetween τ.laminar hF hFsub).1
      τ.isNormal_F₁ hNF).HasNoPrintedSubTubeOf r (s + 2) := by
  have : T2Space S := τ.t2Space
  let h₁F := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hF hFsub).1
  let ξ := τ.subTube h₁F τ.isNormal_F₁ hNF
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hFpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hF hle).mp hFsub
  rintro ⟨A, B, hab, hAsub, hBsub, hNA, hNB, hw, hl⟩
  have hA : IsHoop A := hab.2.1
  have hB : IsHoop B := hab.2.2.1
  have hApos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ hF hA hFpos.1).mp hAsub
  have hBpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ hF hB hFpos.1).mp hBsub
  have hNA' : τ.Γ.IsNormal A :=
    (τ.subTube_isNormal_iff h₁F τ.isNormal_F₁ hNF hAsub).mp hNA
  have hNB' : τ.Γ.IsNormal B :=
    (τ.subTube_isNormal_iff h₁F τ.isNormal_F₁ hNF hBsub).mp hNB
  have heq : ξ.subTube hab hNA hNB = τ.subTube hab hNA' hNB' :=
    τ.subTube_subTube h₁F τ.isNormal_F₁ hNF hab hAsub hBsub hNA hNB
  rcases (cap.areLaminarHoops_iff τ.isCylinder hA hB).mp hab with hAB | hBA
  · have hswap : (τ.subTube hab hNA' hNB').symm = τ.subTube hab.symm hNB' hNA' := by
      apply Tube.ext
      · change τ.Γ.interSet (cylinderBetween A B) = τ.Γ.interSet (cylinderBetween B A)
        rw [cylinderBetween_comm]
      · rfl
      · rfl
    have hw' : (r : ℕ∞) ≤ (τ.subTube hab.symm hNB' hNA').printedWidth := by
      rw [← hswap, Tube.printedWidth_symm, ← heq]
      exact hw
    have hl' : s + 2 ≤ (τ.subTube hab.symm hNB' hNA').length := by
      rw [← hswap, Tube.length_symm, ← heq]
      exact hl
    exact hnot (τ.printedBoundaryLinked_of_long_tube_before_closest cap hpositive hle hcount hglobal
      hF hB hA hFsub hmin hApos.1 hAB hBpos.2 hNB' hNA' hw' hl')
  · have hw' : (r : ℕ∞) ≤ (τ.subTube hab hNA' hNB').printedWidth := by
      rw [← heq]
      exact hw
    have hl' : s + 2 ≤ (τ.subTube hab hNA' hNB').length := by
      rw [← heq]
      exact hl
    exact hnot (τ.printedBoundaryLinked_of_long_tube_before_closest cap hpositive hle hcount hglobal
      hF hA hB hFsub hmin hBpos.1 hBA hApos.2 hNA' hNB' hw' hl')

end GraphMinor.GM08
