module

public import GraphMinor.GM08.Section15Portions

/-!
# Graph Minors VIII, printed (15.1): gluing the train

This file states Lemma 4 of the proof of the printed (15.1) in `Section15PrintedFinal.lean` for the
part of a tube between two of its
hoops (`Tube.lemma4_sub`), and glues the parts of `GM08/Section15Portions.lean` into a train:
* `Tube.Framing.left_step` adds the padded bridges of a pocket found by Lemma 4;
* `Tube.Framing.assemble` glues a left part, a middle where every hoop has at least `r`
  vertices, and a right part;
* `Tube.Framing.assemble_left` glues a left part and a middle that reaches the second end.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}

/-- **Lemma 4 between two hoops.** `Tube.lemma4` for the sub-tube between laminar normal hoops
`H₁`, `H₂`, written with the vertices of the whole drawing. It gives a hoop `L` with the vertices
of `H₁` (the far side of the pocket), a vertex `v`, and a hoop `H` with the vertices of `L` and
`v`, such that the drawing between `L` and `H₂` lies between `H` and `H₂`, and no hoop between
`H` and `H₂` has the vertices of `H₁`. -/
theorem Tube.lemma4_sub (τ : Tube S) {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween H₁ H₂ →
      (H₁ ∩ τ.Γ.V).ncard ≤ (F ∩ τ.Γ.V).ncard)
    (hBA : ∃ x ∈ H₂ ∩ τ.Γ.V, x ∉ H₁) :
    ∃ L : Set S, IsHoop L ∧ τ.Γ.IsNormal L ∧ L ⊆ cylinderBetween H₁ H₂ ∧
      L ∩ τ.Γ.V = H₁ ∩ τ.Γ.V ∧
      ∃ v ∈ τ.Γ.V, v ∉ L ∧ ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧
        H ⊆ cylinderBetween L H₂ ∧ H ∩ τ.Γ.V = insert v (L ∩ τ.Γ.V) ∧
        τ.Γ.U ∩ cylinderBetween L H₂ ⊆ cylinderBetween H H₂ ∧
        ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween H H₂ →
          F ∩ τ.Γ.V ≠ H₁ ∩ τ.Γ.V := by
  have : T2Space S := τ.t2Space
  have hcl := isClosed_cylinderBetween hlam
  set σ := τ.subTube hlam hN₁ hN₂ with hσ
  have hσV : σ.Γ.V = τ.Γ.V ∩ cylinderBetween H₁ H₂ := interSet_V_of_isClosed τ.Γ hcl
  have hσU : σ.Γ.U = τ.Γ.U ∩ cylinderBetween H₁ H₂ :=
    interSet_U_eq_of_laminar_normal τ.Γ hlam hN₁ hN₂
  have hFV : ∀ F ⊆ cylinderBetween H₁ H₂, F ∩ σ.Γ.V = F ∩ τ.Γ.V := fun F hF => by
    rw [hσV, ← inter_assoc, inter_eq_left.mpr
      (show F ∩ τ.Γ.V ⊆ cylinderBetween H₁ H₂ from inter_subset_left.trans hF)]
  have hH₁ := subset_cylinderBetween_left hlam
  have hH₂ := subset_cylinderBetween_right hlam
  obtain ⟨L, hL, hNL, hLsub, hLV, -, v, hvV, hvL, H, hH, hNH, hHsub, hHV, hcov, hne⟩ :=
    σ.lemma4 (fun F hF hN hsub => by
      change (H₁ ∩ σ.Γ.V).ncard ≤ (F ∩ σ.Γ.V).ncard
      rw [hFV H₁ hH₁, hFV F hsub]
      exact hmin F hF ((τ.subTube_isNormal_iff hlam hN₁ hN₂ hsub).mp hN) hsub)
      (by
        obtain ⟨x, ⟨hx, hxV⟩, hx1⟩ := hBA
        exact ⟨x, ⟨hx, hσV ▸ ⟨hxV, hH₂ hx⟩⟩, hx1⟩)
  change L ⊆ cylinderBetween H₁ H₂ at hLsub
  change H ⊆ cylinderBetween L H₂ at hHsub
  have hLH₂ := (areLaminarHoops_of_subset_cylinderBetween hlam hL hLsub).2
  have hsubLH₂ : cylinderBetween L H₂ ⊆ cylinderBetween H₁ H₂ :=
    cylinderBetween_subset_cylinderBetween hlam hLH₂ hLsub hH₂
  have hHH₂ := (areLaminarHoops_of_subset_cylinderBetween hLH₂ hH hHsub).2
  have hsubHH₂ : cylinderBetween H H₂ ⊆ cylinderBetween H₁ H₂ :=
    (cylinderBetween_subset_cylinderBetween hLH₂ hHH₂ hHsub
      (subset_cylinderBetween_right hLH₂)).trans hsubLH₂
  refine ⟨L, hL, (τ.subTube_isNormal_iff hlam hN₁ hN₂ hLsub).mp hNL, hLsub, ?_, v,
    (hσV ▸ hvV).1, hvL, H, hH, (τ.subTube_isNormal_iff hlam hN₁ hN₂ (hHsub.trans hsubLH₂)).mp hNH,
    hHsub, ?_, ?_, ?_⟩
  · rw [← hFV L hLsub, ← hFV H₁ hH₁]
    exact hLV
  · rw [← hFV H (hHsub.trans hsubLH₂), ← hFV L hLsub]
    exact hHV
  · rintro z ⟨hzU, hz⟩
    exact hcov ⟨hσU ▸ ⟨hzU, hsubLH₂ hz⟩, hz⟩
  · intro F hF hN hsub heq
    refine hne F hF ((τ.subTube_isNormal_iff hlam hN₁ hN₂ (hsub.trans hsubHH₂)).mpr hN) hsub ?_
    change F ∩ σ.Γ.V = H₁ ∩ σ.Γ.V
    rw [hFV F (hsub.trans hsubHH₂), hFV H₁ hH₁]
    exact heq

/-- If the drawing between `L'` and `H₂` lies between `L⁺` and `H₂`, for hoops in the order
`L'`, `L⁺`, `H₂`, then the drawing between `L'` and `L⁺` lies on `L⁺`. -/
theorem Tube.strip_of_cover (τ : Tube S) (cap : CylinderSphereCap S) {L' L H₂ : Set S}
    (hL' : IsHoop L') (hL : IsHoop L) (hH₂ : IsHoop H₂)
    (le₁ : cap.disc₁ τ.isCylinder.1 hL' ⊆ cap.disc₁ τ.isCylinder.1 hL)
    (le₂ : cap.disc₁ τ.isCylinder.1 hL ⊆ cap.disc₁ τ.isCylinder.1 hH₂)
    (hcov : τ.Γ.U ∩ cylinderBetween L' H₂ ⊆ cylinderBetween L H₂) :
    τ.Γ.U ∩ cylinderBetween L' L ⊆ L := by
  have hS := τ.isCylinder
  have hmono : cylinderBetween L' L ⊆ cylinderBetween L' H₂ :=
    cap.cylinderBetween_mono hS hL' hL' hL hH₂ subset_rfl le₁ le₂
  rintro z ⟨hzU, hz⟩
  rw [← cap.cylinderBetween_inter hS hL' hL hH₂ le₁ le₂]
  exact ⟨hz, hcov ⟨hzU, hmono hz⟩⟩

namespace Tube.Framing

variable {τ : Tube S} {X : Graft α β}

theorem vertsIn_eq_of_inter_eq (fr : τ.Framing X) {H H' : Set S}
    (h : H ∩ τ.Γ.V = H' ∩ τ.Γ.V) : fr.vertsIn H = fr.vertsIn H' := by
  ext x
  constructor
  · rintro ⟨hx, hxH⟩
    exact ⟨hx, (h ▸ ⟨hxH, (fr.iso.vertexEquiv ⟨x, hx⟩).2⟩ : _ ∈ H' ∩ τ.Γ.V).1⟩
  · rintro ⟨hx, hxH⟩
    exact ⟨hx, (h.symm ▸ ⟨hxH, (fr.iso.vertexEquiv ⟨x, hx⟩).2⟩ : _ ∈ H ∩ τ.Γ.V).1⟩

theorem vertsIn_subset_of_inter_subset (fr : τ.Framing X) {H H' : Set S}
    (h : H ∩ τ.Γ.V ⊆ H' ∩ τ.Γ.V) : fr.vertsIn H ⊆ fr.vertsIn H' :=
  fun x ⟨hx, hxH⟩ => ⟨hx, (h ⟨hxH, (fr.iso.vertexEquiv ⟨x, hx⟩).2⟩).1⟩

/-- **A pocket step of the left part.** `decomposes_step` with the first hoop `F₁` of the tube,
and with the junction `J` the vertices of a hoop `Lf` that comes after the pocket. -/
theorem left_step (fr : τ.Framing X) (cap : CylinderSphereCap S) {H L' L'' Lf : Set S}
    (hH : IsHoop H) (hL' : IsHoop L') (hL'' : IsHoop L'') (hLf : IsHoop Lf)
    (hNH : τ.Γ.IsNormal H) (hNL' : τ.Γ.IsNormal L') (hNL'' : τ.Γ.IsNormal L'')
    (le₁ : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hH)
    (le₂ : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 hL')
    (le₃ : cap.disc₁ τ.isCylinder.1 hL' ⊆ cap.disc₁ τ.isCylinder.1 hL'')
    (le₄ : cap.disc₁ τ.isCylinder.1 hL'' ⊆ cap.disc₁ τ.isCylinder.1 hLf)
    (le₅ : cap.disc₁ τ.isCylinder.1 hLf ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (hpocket : fr.vertsIn H = fr.vertsIn L') (hstrip : τ.Γ.U ∩ cylinderBetween L' L'' ⊆ L'')
    {A Y₁' : Set α} {r t u : ℕ} (hHJ : fr.vertsIn H ⊆ fr.vertsIn Lf)
    (hL''J : fr.vertsIn L'' ⊆ fr.vertsIn Lf) (ht : t ≤ r + 1) (hu : r ≤ u)
    (hr : (fr.vertsIn Lf).ncard = r)
    (hD : Decomposes (printedTubularClass t u) X
      (fr.vertsIn (cylinderBetween τ.F₁ H) ∪ fr.vertsIn Lf) (fr.edgesIn (cylinderBetween τ.F₁ H))
      A (fr.vertsIn Lf) Y₁' (fr.vertsIn Lf) r) :
    Decomposes (printedTubularClass t u) X
      (fr.vertsIn (cylinderBetween τ.F₁ L'') ∪ fr.vertsIn Lf)
      (fr.edgesIn (cylinderBetween τ.F₁ L'')) A (fr.vertsIn Lf) (fr.vertsIn Lf) (fr.vertsIn Lf)
      r := by
  have hS := τ.isCylinder
  have hLfsub : Lf ⊆ cylinderBetween L' τ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff hS hL' τ.isHoop_F₂ hLf
      (le₃.trans (le₄.trans le₅))).mpr ⟨le₃.trans le₄, le₅⟩
  have hHL' : cylinderBetween H L' ⊆ cylinderBetween τ.F₁ L' :=
    cap.cylinderBetween_mono hS τ.isHoop_F₁ hH hL' hL' le₁ le₂ subset_rfl
  have hint := (fr.split cap τ.isHoop_F₁ hL' τ.isHoop_F₂ hNL' (le₁.trans le₂)
    (le₃.trans (le₄.trans le₅))).2.1
  have hJin : fr.vertsIn Lf ∩ fr.vertsIn (cylinderBetween H L') ⊆ fr.vertsIn H := by
    rintro x ⟨hx1, hx2⟩
    rw [hpocket, ← hint]
    exact ⟨fr.vertsIn_mono hHL' hx2, fr.vertsIn_mono hLfsub hx1⟩
  exact fr.decomposes_step cap τ.isHoop_F₁ hH hL' hL'' hNH hNL' hNL'' le₁ le₂ le₃ hpocket hstrip
    (fr.vertsIn_subset_V _) hHJ hJin hL''J (by rw [hr]; exact ht) (by rw [hr]; exact hu) hr hD

/-- **Gluing the train.** Let `L`, `R` be normal hoops in this order, each with `r` vertices, such
that every normal hoop between them carries at least `r` vertices. Given decompositions of the
part before `L` from the first end to `L`, and of the part after `R` from `R` to the second end,
with all inner junctions those of `L` and of `R`, the graft is an `r`-train. -/
theorem assemble (fr : τ.Framing X) (cap : CylinderSphereCap S) {L R : Set S} (hL : IsHoop L)
    (hR : IsHoop R) (hNL : τ.Γ.IsNormal L) (hNR : τ.Γ.IsNormal R)
    (le₁ : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hL)
    (le₂ : cap.disc₁ τ.isCylinder.1 hL ⊆ cap.disc₁ τ.isCylinder.1 hR)
    (le₃ : cap.disc₁ τ.isCylinder.1 hR ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂) {r k : ℕ}
    (hJ : (fr.vertsIn L).ncard = r) (hK : (fr.vertsIn R).ncard = r)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween L R →
      r ≤ (F ∩ τ.Γ.V).ncard)
    (hleft : Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
      (fr.vertsIn (cylinderBetween τ.F₁ L)) (fr.edgesIn (cylinderBetween τ.F₁ L))
      (fr.vertsIn τ.F₁) (fr.vertsIn L) (fr.vertsIn L) (fr.vertsIn L) r)
    (hright : Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
      (fr.vertsIn (cylinderBetween R τ.F₂)) (fr.edgesIn (cylinderBetween R τ.F₂))
      (fr.vertsIn R) (fr.vertsIn R) (fr.vertsIn R) (fr.vertsIn τ.F₂) r) :
    X ∈ LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hlam : ∀ {F₁ F₂ : Set S} (h₁ : IsHoop F₁) (h₂ : IsHoop F₂),
      cap.disc₁ hS.1 h₁ ⊆ cap.disc₁ hS.1 h₂ → AreLaminarHoops F₁ F₂ :=
    fun h₁ h₂ hle => (cap.areLaminarHoops_iff hS h₁ h₂).mpr (.inl hle)
  obtain ⟨Y₀', Y₁', hM, hJK, -⟩ := fr.decomposes_middle (hlam hL hR le₂) hNL hNR (k := k) hmin
    (by omega) (by omega)
    (by have := ncard_union_le (fr.vertsIn L) (fr.vertsIn R); omega)
  obtain ⟨hV1, hI1, hE1, hD1⟩ := fr.split cap τ.isHoop_F₁ hL hR hNL le₁ le₂
  obtain ⟨hV2, hI2, hE2, hD2⟩ := fr.split cap τ.isHoop_F₁ hR τ.isHoop_F₂ hNR (le₁.trans le₂) le₃
  have hcl : ∀ {F₁ F₂ : Set S} (h₁ : IsHoop F₁) (h₂ : IsHoop F₂),
      cap.disc₁ hS.1 h₁ ⊆ cap.disc₁ hS.1 h₂ → IsClosed (cylinderBetween F₁ F₂) :=
    fun h₁ h₂ hle => isClosed_cylinderBetween (hlam h₁ h₂ hle)
  have hends : ∀ {F₁ F₂ : Set S} (h₁ : IsHoop F₁) (h₂ : IsHoop F₂),
      cap.disc₁ hS.1 h₁ ⊆ cap.disc₁ hS.1 h₂ →
      ∀ e ∈ fr.edgesIn (cylinderBetween F₁ F₂), ∀ x y, X.G.IsLink e x y →
        x ∈ fr.vertsIn (cylinderBetween F₁ F₂) :=
    fun h₁ h₂ hle _ he _ _ hl => (fr.ends_mem_vertsIn_of_isClosed (hcl h₁ h₂ hle) he hl).1
  have h1 := (hleft.append hM (fr.edgesIn_subset_E _) (fr.edgesIn_subset_E _)
    (hends τ.isHoop_F₁ hL le₁) (hends hL hR le₂) hI1 hD1 hJ).congr_sets hV1 hE1
  have h2 := (h1.append hright (fr.edgesIn_subset_E _) (fr.edgesIn_subset_E _)
    (hends τ.isHoop_F₁ hR (le₁.trans le₂)) (hends hR τ.isHoop_F₂ le₃) hI2 hD2 hK).congr_sets
    (hV2.trans fr.vertsIn_cylinderBetween_F) (hE2.trans fr.edgesIn_cylinderBetween_F)
  exact h2.mem_LKGraftClass fr.vertsIn_F_union.symm hJK

/-- **Gluing the train without a right part.** As `assemble`, when every normal hoop between `L`
and the second end, other than those with the vertices of the second end, carries at least `r`
vertices, and the second end carries at most `k + r` vertices. -/
theorem assemble_left (fr : τ.Framing X) (cap : CylinderSphereCap S) {L : Set S} (hL : IsHoop L)
    (hNL : τ.Γ.IsNormal L)
    (le₁ : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hL)
    (le₂ : cap.disc₁ τ.isCylinder.1 hL ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂) {r k : ℕ}
    (hJ : (fr.vertsIn L).ncard = r) (hB : (fr.vertsIn τ.F₂).ncard ≤ k + r)
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween L τ.F₂ →
      r ≤ (F ∩ τ.Γ.V).ncard)
    (hleft : Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
      (fr.vertsIn (cylinderBetween τ.F₁ L)) (fr.edgesIn (cylinderBetween τ.F₁ L))
      (fr.vertsIn τ.F₁) (fr.vertsIn L) (fr.vertsIn L) (fr.vertsIn L) r) :
    X ∈ LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hlam : ∀ {F₁ F₂ : Set S} (h₁ : IsHoop F₁) (h₂ : IsHoop F₂),
      cap.disc₁ hS.1 h₁ ⊆ cap.disc₁ hS.1 h₂ → AreLaminarHoops F₁ F₂ :=
    fun h₁ h₂ hle => (cap.areLaminarHoops_iff hS h₁ h₂).mpr (.inl hle)
  obtain ⟨Y₀', Y₁', hM, -, hlink⟩ := fr.decomposes_middle (hlam hL τ.isHoop_F₂ le₂) hNL
    τ.isNormal_F₂ (k := k) hmin (by omega) hB
    (by have := ncard_union_le (fr.vertsIn L) (fr.vertsIn τ.F₂); omega)
  obtain ⟨hV1, hI1, hE1, hD1⟩ := fr.split cap τ.isHoop_F₁ hL τ.isHoop_F₂ hNL le₁ le₂
  have h1 := (hleft.append hM (fr.edgesIn_subset_E _) (fr.edgesIn_subset_E _)
    (fun _ he _ _ hl => (fr.ends_mem_vertsIn_of_isClosed
      (isClosed_cylinderBetween (hlam τ.isHoop_F₁ hL le₁)) he hl).1)
    (fun _ he _ _ hl => (fr.ends_mem_vertsIn_of_isClosed
      (isClosed_cylinderBetween (hlam hL τ.isHoop_F₂ le₂)) he hl).1) hI1 hD1 hJ).congr_sets
    (hV1.trans fr.vertsIn_cylinderBetween_F) (hE1.trans fr.edgesIn_cylinderBetween_F)
  exact h1.mem_LKGraftClass fr.vertsIn_F_union.symm (hlink hJ)

end Tube.Framing

end GraphMinor.GM08
